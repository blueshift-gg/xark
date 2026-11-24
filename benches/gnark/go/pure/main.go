// The benchmark's reference: the circuits of `benches/gnark/` written directly
// against gnark's frontend, compiled, set up and proved by gnark alone.
//
//	go run ./pure <sha256|keccak256|sha256_1024|keccak256_1024|poseidon2|poseidon2_chain> <runs>
//	go run ./pure inputs <sha256|keccak256|sha256_1024|keccak256_1024>
//
// The first prints `constraints=<n>`, `prove_ms=<median of the runs>` with every
// core and `prove_1_ms` on one thread, as `../iden3` does for the
// xark-compiled circuit. The second prints the
// same message and digest as the inputs of the xark circuit (`xark prove
// --inputs`), so the two sides prove one statement and `run.sh` keeps no copy.
package main

import (
	stdsha256 "crypto/sha256"
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"runtime"
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
	"github.com/consensys/gnark/std/hash"
	"github.com/consensys/gnark/std/hash/sha2"
	"github.com/consensys/gnark/std/hash/sha3"
	"github.com/consensys/gnark/std/math/uints"
	"github.com/consensys/gnark/std/permutation/poseidon2"
	nativesha3 "golang.org/x/crypto/sha3"
)

// The size of `poseidon2_chain/src/lib.rs`.
const chainPermutations = 1000

// Poseidon2 as xark-poseidon2 has it: t = 3, R_F = 8, R_P = 56, x^5. gnark-crypto
// derives its own round constants, so the two compute different permutations of
// the same shape and cost.
const (
	width         = 3
	fullRounds    = 8
	partialRounds = 56
)

// Digest is `examples/sha256` or `examples/keccak256` (the three bytes "abc"), or
// `sha256_1024` or `keccak256_1024` (1024 bytes): a private message whose digest
// is public as two 128-bit halves (xark-hash's `Hash`), high half first. `keccak`
// picks Keccak-256 (Ethereum's) over SHA-256.
type Digest struct {
	Msg    []frontend.Variable
	Hi, Lo frontend.Variable `gnark:",public"`
	keccak bool
}

func (c *Digest) Define(api frontend.API) error {
	bytes, err := uints.New[uints.U32](api)
	if err != nil {
		return err
	}
	var h hash.BinaryFixedLengthHasher
	if c.keccak {
		h, err = sha3.NewLegacyKeccak256(api)
	} else {
		h, err = sha2.New(api)
	}
	if err != nil {
		return err
	}
	// A message byte is range-checked on the way in, as a xark `u8` input is.
	msg := make([]uints.U8, len(c.Msg))
	for i := range msg {
		msg[i] = bytes.ByteValueOf(c.Msg[i])
	}
	h.Write(msg)
	digest := h.Sum()
	half := func(b []uints.U8) frontend.Variable {
		var acc frontend.Variable = 0
		for _, v := range b {
			acc = api.Add(api.Mul(acc, 256), v.Val)
		}
		return acc
	}
	api.AssertIsEqual(half(digest[:16]), c.Hi)
	api.AssertIsEqual(half(digest[16:]), c.Lo)
	return nil
}

// message is the benchmark's message of `size` bytes and its digest: "abc", or
// the bytes 0, 1, …, 255 over and over, as the xark circuits' tests.
func message(keccak bool, size int) (msg, sum []byte) {
	msg = []byte("abc")
	if size != len(msg) {
		msg = make([]byte, size)
		for i := range msg {
			msg[i] = byte(i)
		}
	}
	if keccak {
		h := nativesha3.NewLegacyKeccak256()
		h.Write(msg)
		return msg, h.Sum(nil)
	}
	s := stdsha256.Sum256(msg)
	return msg, s[:]
}

// xarkInputs is the message and its digest under the names the xark circuit
// gives them: `msg[i]`, and the digest's halves `digest.hi` and `digest.lo`.
func xarkInputs(keccak bool, size int) ([]byte, error) {
	msg, sum := message(keccak, size)
	inputs := map[string]string{
		"digest.hi": new(big.Int).SetBytes(sum[:16]).String(),
		"digest.lo": new(big.Int).SetBytes(sum[16:]).String(),
	}
	for i, b := range msg {
		inputs["msg["+strconv.Itoa(i)+"]"] = strconv.Itoa(int(b))
	}
	return json.Marshal(inputs)
}

// digests are the digest circuits: Keccak-256 or SHA-256, and the message's size.
var digests = map[string]struct {
	keccak bool
	size   int
}{
	"sha256":         {false, 3},
	"keccak256":      {true, 3},
	"sha256_1024":    {false, 1024},
	"keccak256_1024": {true, 1024},
}

func digestPair(keccak bool, size int) (circuit, assignment frontend.Circuit) {
	msg, sum := message(keccak, size)
	a := &Digest{
		Msg: make([]frontend.Variable, size),
		Hi:  new(big.Int).SetBytes(sum[:16]),
		Lo:  new(big.Int).SetBytes(sum[16:]),
	}
	for i := range msg {
		a.Msg[i] = msg[i]
	}
	return &Digest{Msg: make([]frontend.Variable, size), keccak: keccak}, a
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

func main() {
	logger.Disable()
	if err := run(os.Args[1:]); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run(args []string) error {
	usage := fmt.Errorf("usage: pure-gnark <circuit> <runs> | inputs <circuit>, a circuit one of sha256, keccak256, sha256_1024, keccak256_1024, poseidon2, poseidon2_chain (inputs: the first four)")
	if len(args) != 2 {
		return usage
	}
	if args[0] == "inputs" {
		d, ok := digests[args[1]]
		if !ok {
			return usage
		}
		inputs, err := xarkInputs(d.keccak, d.size)
		if err != nil {
			return err
		}
		fmt.Println(string(inputs))
		return nil
	}
	runs, err := strconv.Atoi(args[1])
	if err != nil || runs < 1 {
		return usage
	}
	var circuit, assignment frontend.Circuit
	if d, ok := digests[args[0]]; ok {
		circuit, assignment = digestPair(d.keccak, d.size)
	} else {
		switch args[0] {
		case "poseidon2":
			circuit, assignment = poseidon2Pair(1)
		case "poseidon2_chain":
			circuit, assignment = poseidon2Pair(chainPermutations)
		default:
			return usage
		}
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
	fmt.Printf("constraints=%d\n", ccs.GetNbConstraints())
	for round, name := range []string{"prove_ms", "prove_1_ms"} {
		times := make([]time.Duration, runs)
		for i := range times {
			start := time.Now()
			proof, err := groth16.Prove(ccs, pk, w)
			if err != nil {
				return err
			}
			times[i] = time.Since(start)
			if round == 0 && i == 0 {
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
		fmt.Printf("%s=%s\n", name, strconv.FormatFloat(float64(times[runs/2].Microseconds())/1000, 'f', 3, 64))
		// The second round runs on one thread; the compile and the setup did
		// not have to.
		runtime.GOMAXPROCS(1)
	}
	return nil
}
