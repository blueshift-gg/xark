// The benchmark's reference: the circuits of `benches/gnark/` written directly
// against gnark's frontend, compiled, set up and proved by gnark alone.
//
//	go run . <fibonacci|poseidon2|poseidon2_chain> <runs>
//
// Prints `constraints=<n>` and `prove_ms=<median of the runs>`, as `xark-gnark
// bench` does for the xark-compiled circuit.
package main

import (
	"fmt"
	"os"
	"sort"
	"strconv"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	native "github.com/consensys/gnark-crypto/ecc/bn254/fr/poseidon2"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/logger"
	"github.com/consensys/gnark/std/permutation/poseidon2"
)

// The sizes of `fibonacci/src/lib.rs` and `poseidon2_chain/src/lib.rs`.
const (
	fibonacciSteps    = 1000
	chainPermutations = 1000
)

// Poseidon2 as xark-poseidon2 has it: t = 3, R_F = 8, R_P = 56, x^5. gnark-crypto
// derives its own round constants, so the two compute different permutations of
// the same shape and cost.
const (
	width         = 3
	fullRounds    = 8
	partialRounds = 56
)

// Fibonacci is `fibonacci/src/lib.rs`: private A0, A1, public Result after
// `fibonacciSteps` additions.
type Fibonacci struct {
	A0, A1 frontend.Variable
	Result frontend.Variable `gnark:",public"`
}

func (c *Fibonacci) Define(api frontend.API) error {
	a, b := c.A0, c.A1
	for i := 0; i < fibonacciSteps; i++ {
		a, b = b, api.Add(a, b)
	}
	api.AssertIsEqual(b, c.Result)
	return nil
}

// Poseidon2 is `examples/poseidon2` (one permutation) or `poseidon2_chain` (a
// thousand): a private state permuted `n` times to a public one.
type Poseidon2 struct {
	In  [width]frontend.Variable
	Out [width]frontend.Variable `gnark:",public"`
	n   int
}

func (c *Poseidon2) Define(api frontend.API) error {
	h, err := poseidon2.NewPoseidon2FromParameters(api, width, fullRounds, partialRounds)
	if err != nil {
		return err
	}
	state := c.In[:]
	state = append([]frontend.Variable(nil), state...)
	for i := 0; i < c.n; i++ {
		if err := h.Permutation(state); err != nil {
			return err
		}
	}
	for i := range state {
		api.AssertIsEqual(state[i], c.Out[i])
	}
	return nil
}

func poseidon2Pair(n int) (circuit, assignment frontend.Circuit) {
	state := []fr.Element{fr.NewElement(1), fr.NewElement(2), fr.NewElement(3)}
	a := &Poseidon2{n: n}
	for i := range state {
		a.In[i] = state[i]
	}
	h := native.NewPermutation(width, fullRounds, partialRounds)
	for i := 0; i < n; i++ {
		if err := h.Permutation(state); err != nil {
			panic(err)
		}
	}
	for i := range state {
		a.Out[i] = state[i]
	}
	return &Poseidon2{n: n}, a
}

func fibonacciPair() (circuit, assignment frontend.Circuit) {
	var a, b fr.Element
	a.SetOne()
	b.SetOne()
	for i := 0; i < fibonacciSteps; i++ {
		a, b = b, *new(fr.Element).Add(&a, &b)
	}
	return &Fibonacci{}, &Fibonacci{A0: 1, A1: 1, Result: b}
}

func main() {
	logger.Disable()
	if err := run(os.Args[1:]); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run(args []string) error {
	const usage = "usage: xark-gnark-bench <fibonacci|poseidon2|poseidon2_chain> <runs>"
	if len(args) != 2 {
		return fmt.Errorf(usage)
	}
	runs, err := strconv.Atoi(args[1])
	if err != nil || runs < 1 {
		return fmt.Errorf(usage)
	}
	var circuit, assignment frontend.Circuit
	switch args[0] {
	case "fibonacci":
		circuit, assignment = fibonacciPair()
	case "poseidon2":
		circuit, assignment = poseidon2Pair(1)
	case "poseidon2_chain":
		circuit, assignment = poseidon2Pair(chainPermutations)
	default:
		return fmt.Errorf(usage)
	}
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, circuit)
	if err != nil {
		return err
	}
	pk, vk, err := groth16.Setup(ccs)
	if err != nil {
		return err
	}
	w, err := frontend.NewWitness(assignment, ecc.BN254.ScalarField())
	if err != nil {
		return err
	}
	times := make([]time.Duration, runs)
	for i := range times {
		start := time.Now()
		proof, err := groth16.Prove(ccs, pk, w)
		if err != nil {
			return err
		}
		times[i] = time.Since(start)
		if i == 0 {
			public, err := w.Public()
			if err != nil {
				return err
			}
			if err := groth16.Verify(proof, vk, public); err != nil {
				return err
			}
		}
	}
	sort.Slice(times, func(i, j int) bool { return times[i] < times[j] })
	fmt.Printf("constraints=%d\n", ccs.GetNbConstraints())
	fmt.Printf("prove_ms=%s\n", strconv.FormatFloat(float64(times[runs/2].Microseconds())/1000, 'f', 3, 64))
	return nil
}
