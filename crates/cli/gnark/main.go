// xark-gnark proves xark circuits with gnark's Groth16 (BN254).
//
// `xark setup|prove|verify --backend gnark` drives it. xark hands over the
// circuit as an iden3 `.r1cs` file and the solved witness as an iden3 `.wtns`
// file; this tool turns the rows into a gnark constraint system (`circuit.ccs`,
// readable by any gnark program with `groth16.NewCS(ecc.BN254).ReadFrom`) and
// runs gnark's setup, prover and verifier on it.
//
// Every xark variable becomes a gnark input wire (the public inputs public, the
// rest secret) and none an internal one: xark's solver has already computed the
// whole witness, so gnark's solver has nothing to derive and only checks each
// row before proving.
package main

import (
	"bufio"
	"encoding/binary"
	"fmt"
	"io"
	"math/big"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
	cs_bn254 "github.com/consensys/gnark/constraint/bn254"
	"github.com/consensys/gnark/logger"
)

const usage = `usage:
  xark-gnark convert <circuit.r1cs> <circuit.ccs>
  xark-gnark setup   <circuit.r1cs> <key dir>
  xark-gnark prove   <key dir> <witness.wtns> <out dir>
  xark-gnark verify  <vk.bin> <proof.bin> <public_witness.bin>
  xark-gnark bench   <key dir> <witness.wtns> <runs>`

func main() {
	logger.Disable()
	if err := run(os.Args[1:]); err != nil {
		fmt.Fprintln(os.Stderr, "xark-gnark:", err)
		os.Exit(1)
	}
}

func run(args []string) error {
	switch {
	case len(args) == 3 && args[0] == "convert":
		ccs, err := readR1CS(args[1])
		if err != nil {
			return err
		}
		return writeTo(args[2], ccs)
	case len(args) == 3 && args[0] == "setup":
		return setup(args[1], args[2])
	case len(args) == 4 && args[0] == "prove":
		return prove(args[1], args[2], args[3])
	case len(args) == 4 && args[0] == "verify":
		return verify(args[1], args[2], args[3])
	case len(args) == 4 && args[0] == "bench":
		runs, err := strconv.Atoi(args[3])
		if err != nil || runs < 1 {
			return fmt.Errorf("%s", usage)
		}
		return bench(args[1], args[2], runs)
	}
	return fmt.Errorf("%s", usage)
}

func setup(r1csPath, dir string) error {
	ccs, err := readR1CS(r1csPath)
	if err != nil {
		return err
	}
	if err := writeTo(filepath.Join(dir, "circuit.ccs"), ccs); err != nil {
		return err
	}
	start := time.Now()
	pk, vk, err := groth16.Setup(ccs)
	if err != nil {
		return fmt.Errorf("setup: %w", err)
	}
	report("setup_ms", time.Since(start))
	// Raw (uncompressed) points: the key is read back on every proof.
	if err := writeRawTo(filepath.Join(dir, "pk.bin"), pk); err != nil {
		return err
	}
	if err := writeTo(filepath.Join(dir, "vk.bin"), vk); err != nil {
		return err
	}
	fmt.Printf("constraints=%d\n", ccs.GetNbConstraints())
	fmt.Printf("public=%d\n", ccs.GetNbPublicVariables()-1)
	fmt.Printf("secret=%d\n", ccs.GetNbSecretVariables())
	return nil
}

// load reads what a proof needs: the constraint system and keys `setup` wrote,
// and the witness xark solved.
func load(dir, wtnsPath string) (constraint.ConstraintSystem, groth16.ProvingKey, groth16.VerifyingKey, witness.Witness, error) {
	ccs := groth16.NewCS(ecc.BN254)
	if err := readFrom(filepath.Join(dir, "circuit.ccs"), ccs); err != nil {
		return nil, nil, nil, nil, err
	}
	pk := groth16.NewProvingKey(ecc.BN254)
	if err := readFrom(filepath.Join(dir, "pk.bin"), unsafeReader{pk}); err != nil {
		return nil, nil, nil, nil, err
	}
	vk := groth16.NewVerifyingKey(ecc.BN254)
	if err := readFrom(filepath.Join(dir, "vk.bin"), vk); err != nil {
		return nil, nil, nil, nil, err
	}
	w, err := readWitness(wtnsPath, ccs.GetNbPublicVariables()-1, ccs.GetNbSecretVariables())
	return ccs, pk, vk, w, err
}

// bench proves the same witness `runs` times with the key resident and reports
// the median (`benches/gnark/run.sh`).
func bench(dir, wtnsPath string, runs int) error {
	ccs, pk, _, w, err := load(dir, wtnsPath)
	if err != nil {
		return err
	}
	times := make([]time.Duration, runs)
	for i := range times {
		start := time.Now()
		if _, err := groth16.Prove(ccs, pk, w); err != nil {
			return fmt.Errorf("prove: %w", err)
		}
		times[i] = time.Since(start)
	}
	sort.Slice(times, func(i, j int) bool { return times[i] < times[j] })
	fmt.Printf("constraints=%d\n", ccs.GetNbConstraints())
	report("prove_ms", times[runs/2])
	return nil
}

func prove(dir, wtnsPath, out string) error {
	ccs, pk, vk, w, err := load(dir, wtnsPath)
	if err != nil {
		return err
	}
	start := time.Now()
	proof, err := groth16.Prove(ccs, pk, w)
	if err != nil {
		return fmt.Errorf("prove: %w", err)
	}
	report("prove_ms", time.Since(start))
	public, err := w.Public()
	if err != nil {
		return err
	}
	start = time.Now()
	if err := groth16.Verify(proof, vk, public); err != nil {
		return fmt.Errorf("the proof does not verify: %w", err)
	}
	report("verify_ms", time.Since(start))
	if err := writeTo(filepath.Join(out, "proof.bin"), proof); err != nil {
		return err
	}
	return writeTo(filepath.Join(out, "public_witness.bin"), public)
}

func verify(vkPath, proofPath, publicPath string) error {
	vk := groth16.NewVerifyingKey(ecc.BN254)
	if err := readFrom(vkPath, vk); err != nil {
		return err
	}
	proof := groth16.NewProof(ecc.BN254)
	if err := readFrom(proofPath, proof); err != nil {
		return err
	}
	public, err := witness.New(ecc.BN254.ScalarField())
	if err != nil {
		return err
	}
	if err := readFrom(publicPath, public); err != nil {
		return err
	}
	if err := groth16.Verify(proof, vk, public); err != nil {
		return fmt.Errorf("the proof does not verify: %w", err)
	}
	return nil
}

// report prints a duration as `name=<milliseconds>`, the form xark and the
// benchmark script read.
func report(name string, d time.Duration) {
	fmt.Printf("%s=%s\n", name, strconv.FormatFloat(float64(d.Microseconds())/1000, 'f', 3, 64))
}

// readR1CS reads an iden3 `.r1cs` file (the format circom writes and snarkjs
// reads: https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md)
// into a gnark R1CS. Wire 0 is the constant one in both; the public wires
// follow it and every other wire is a secret input.
func readR1CS(path string) (constraint.ConstraintSystem, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	r := &reader{r: bufio.NewReaderSize(f, 1<<20)}
	if string(r.bytes(4)) != "r1cs" || r.u32() != 1 {
		return nil, fmt.Errorf("%s: not an iden3 r1cs (version 1) file", path)
	}
	sections := r.u32()
	var ccs *cs_bn254.R1CS
	var gate constraint.BlueprintID
	var fieldSize int
	var rows uint32
	for s := uint32(0); s < sections && r.err == nil; s++ {
		kind, size := r.u32(), r.u64()
		switch {
		case kind == 1:
			fieldSize = int(r.u32())
			if err := checkPrime(r.bytes(fieldSize)); err != nil {
				return nil, fmt.Errorf("%s: %w", path, err)
			}
			wires, pubOut, pubIn := r.u32(), r.u32(), r.u32()
			r.u32() // private inputs: every non-public wire is a secret input here
			r.u64() // labels
			rows = r.u32()
			ccs = cs_bn254.NewR1CS(int(rows))
			ccs.AddPublicVariable("1")
			public := int(pubOut + pubIn)
			for i := 1; i <= public; i++ {
				ccs.AddPublicVariable("public_" + strconv.Itoa(i))
			}
			for i := public + 1; i < int(wires); i++ {
				ccs.AddSecretVariable("w_" + strconv.Itoa(i))
			}
			gate = ccs.AddBlueprint(&constraint.BlueprintGenericR1C{})
		case kind == 2:
			if ccs == nil {
				return nil, fmt.Errorf("%s: the constraints come before the header", path)
			}
			for i := uint32(0); i < rows && r.err == nil; i++ {
				var row constraint.R1C
				row.L = r.lc(ccs, fieldSize)
				row.R = r.lc(ccs, fieldSize)
				row.O = r.lc(ccs, fieldSize)
				ccs.AddR1C(row, gate)
			}
		default:
			r.skip(size)
		}
	}
	if r.err != nil {
		return nil, fmt.Errorf("%s: %w", path, r.err)
	}
	if ccs == nil || ccs.GetNbConstraints() != int(rows) {
		return nil, fmt.Errorf("%s: missing the header or the constraints", path)
	}
	return ccs, nil
}

// readWitness reads an iden3 `.wtns` file (snarkjs' witness format): the value
// of every wire, in wire order, the constant one first.
func readWitness(path string, public, secret int) (witness.Witness, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	r := &reader{r: bufio.NewReaderSize(f, 1<<20)}
	if string(r.bytes(4)) != "wtns" || r.u32() != 2 {
		return nil, fmt.Errorf("%s: not an iden3 wtns (version 2) file", path)
	}
	sections := r.u32()
	var values []fr.Element
	var fieldSize int
	var n uint32
	for s := uint32(0); s < sections && r.err == nil; s++ {
		kind, size := r.u32(), r.u64()
		switch kind {
		case 1:
			fieldSize = int(r.u32())
			if err := checkPrime(r.bytes(fieldSize)); err != nil {
				return nil, fmt.Errorf("%s: %w", path, err)
			}
			n = r.u32()
		case 2:
			values = make([]fr.Element, n)
			for i := range values {
				values[i] = r.element(fieldSize)
			}
		default:
			r.skip(size)
		}
	}
	if r.err != nil {
		return nil, fmt.Errorf("%s: %w", path, r.err)
	}
	if len(values) != 1+public+secret {
		return nil, fmt.Errorf("%s: %d values for a circuit of %d wires (was the key made for another build of the circuit?)", path, len(values), 1+public+secret)
	}
	w, err := witness.New(ecc.BN254.ScalarField())
	if err != nil {
		return nil, err
	}
	ch := make(chan any, 1024)
	go func() {
		for i := 1; i < len(values); i++ {
			ch <- &values[i]
		}
		close(ch)
	}()
	if err := w.Fill(public, secret, ch); err != nil {
		return nil, err
	}
	return w, nil
}

func checkPrime(le []byte) error {
	if new(big.Int).SetBytes(reversed(le)).Cmp(fr.Modulus()) != 0 {
		return fmt.Errorf("not over the BN254 scalar field")
	}
	return nil
}

func reversed(b []byte) []byte {
	out := make([]byte, len(b))
	for i, v := range b {
		out[len(b)-1-i] = v
	}
	return out
}

// reader reads the little-endian iden3 containers, keeping the first error.
type reader struct {
	r   *bufio.Reader
	err error
	buf [64]byte
}

func (r *reader) bytes(n int) []byte {
	if n > len(r.buf) {
		r.err = fmt.Errorf("field elements of %d bytes", n)
	}
	if r.err != nil {
		return r.buf[:0]
	}
	_, r.err = io.ReadFull(r.r, r.buf[:n])
	return r.buf[:n]
}

func (r *reader) u32() uint32 {
	b := r.bytes(4)
	if r.err != nil {
		return 0
	}
	return binary.LittleEndian.Uint32(b)
}

func (r *reader) u64() uint64 {
	b := r.bytes(8)
	if r.err != nil {
		return 0
	}
	return binary.LittleEndian.Uint64(b)
}

func (r *reader) skip(n uint64) {
	if r.err == nil {
		_, r.err = io.CopyN(io.Discard, r.r, int64(n))
	}
}

func (r *reader) element(size int) (e fr.Element) {
	b := r.bytes(size)
	if r.err == nil {
		e.SetBytes(reversed(b))
	}
	return e
}

func (r *reader) lc(ccs *cs_bn254.R1CS, fieldSize int) constraint.LinearExpression {
	n := r.u32()
	if r.err != nil {
		return nil
	}
	lc := make(constraint.LinearExpression, 0, n)
	for i := uint32(0); i < n && r.err == nil; i++ {
		wire := r.u32()
		e := r.element(fieldSize)
		var c constraint.U64
		copy(c[:], e[:])
		lc = append(lc, ccs.MakeTerm(c, int(wire)))
	}
	return lc
}

// unsafeReader reads a proving key without the subgroup checks: the key is this
// tool's own output, and the checks cost more than the proof.
type unsafeReader struct {
	pk groth16.ProvingKey
}

func (u unsafeReader) ReadFrom(r io.Reader) (int64, error) {
	return u.pk.UnsafeReadFrom(r)
}

func readFrom(path string, into io.ReaderFrom) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	if _, err := into.ReadFrom(bufio.NewReaderSize(f, 1<<20)); err != nil {
		return fmt.Errorf("reading %s: %w", path, err)
	}
	return nil
}

func writeTo(path string, from io.WriterTo) error {
	return write(path, from.WriteTo)
}

func writeRawTo(path string, from interface {
	WriteRawTo(io.Writer) (int64, error)
}) error {
	return write(path, from.WriteRawTo)
}

func write(path string, to func(io.Writer) (int64, error)) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	w := bufio.NewWriterSize(f, 1<<20)
	if _, err := to(w); err != nil {
		f.Close()
		return fmt.Errorf("writing %s: %w", path, err)
	}
	if err := w.Flush(); err != nil {
		f.Close()
		return err
	}
	return f.Close()
}
