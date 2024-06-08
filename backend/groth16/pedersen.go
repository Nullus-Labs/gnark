package groth16

import (
	"crypto/rand"
	"fmt"
	"runtime"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

// PedersenKey for proof and verification
type PedersenKey struct {
	basis []bn254.G1Affine
	h     bn254.G1Affine
}

func randomOnG1() (bn254.G1Affine, error) { // TODO: Add to G2.go?
	gBytes := make([]byte, fr.Bytes)
	if _, err := rand.Read(gBytes); err != nil {
		return bn254.G1Affine{}, err
	}
	return bn254.HashToG1(gBytes, []byte("random on g1"))
}

func PedersenSetup(n int) (PedersenKey, error) {
	var (
		k   PedersenKey
		err error
	)

	k.basis = make([]bn254.G1Affine, n)
	for i := range k.basis {
		if k.basis[i], err = randomOnG1(); err != nil {
			return k, err
		}
	}
	k.h, err = randomOnG1()
	return k, err
}

func (k *PedersenKey) Commit(values []fr.Element, r fr.Element) (commitment bn254.G1Affine, err error) {

	if len(values) != len(k.basis) {
		err = fmt.Errorf("unexpected number of values")
		return
	}

	n := runtime.NumCPU()
	// TODO @gbotrel this will spawn more than one task, see
	// https://github.com/ConsenSys/gnark-crypto/issues/269
	config := ecc.MultiExpConfig{
		NbTasks: n, // TODO Experiment
	}

	if _, err = commitment.MultiExp(append(k.basis, k.h), append(values, r), config); err != nil {
		return
	}
	return
}

func (k *PedersenKey) Verify(values []fr.Element, r fr.Element, commitment bn254.G1Affine) error {

	if !commitment.IsInSubGroup() {
		return fmt.Errorf("subgroup check failed")
	}

	if len(values) != len(k.basis) {
		return fmt.Errorf("unexpected number of values")
	}

	c := &bn254.G1Affine{}
	n := runtime.NumCPU()
	if _, err := c.MultiExp(append(k.basis, k.h), append(values, r), ecc.MultiExpConfig{NbTasks: n}); err != nil {
		return err
	}
	if !commitment.Equal(c) {
		return fmt.Errorf("commitment verification failed")
	}
	return nil
}
