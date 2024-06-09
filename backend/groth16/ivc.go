package groth16

import (
	"errors"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	cs "github.com/consensys/gnark/constraint/bn254"
)

type FoldProof struct {
	Primary   CommitedRelaxedR1CS
	Secondary CommitedRelaxedR1CS
}

func IVCSetup(r1cs *cs.R1CS) (pk_e, pk_w PedersenKey, err error) {
	if pk_e, err = PedersenSetup(r1cs.GetNbConstraints()); err != nil {
		return
	}
	if pk_w, err = PedersenSetup(r1cs.GetNbConstraints()); err != nil {
		return
	}
	return
}

func IVCProve(r1cs *cs.R1CS, pk_e, pk_w PedersenKey, witness fr.Vector, num_iter int) (*CommitedRelaxedR1CS, error) {
	if num_iter < 1 {
		return nil, errors.New("invalid number of iterations")
	}
	internal, secret, public := r1cs.GetNbVariables()
	bigInstance, err := NewCommittedRelaxedR1CS(len(r1cs.Coefficients), internal+secret+public, public, pk_e, pk_w)
	if err != nil {
		return nil, err
	}
	comT := bigInstance.Com_E
	// Should pass in the commitment of T to generate the smallInstance
	smallInstance, err := NewCommittedRelaxedR1CSFromInstance(r1cs, witness, pk_e, pk_w)
	if err != nil {
		return nil, err
	}
	_ = comT
	for i := 1; i < num_iter; i++ {
		if bigInstance, comT, err = bigInstance.FoldProve(r1cs, smallInstance, pk_e); err != nil {
			return nil, err
		}
		// TODO: Compute the new witness of F' and generate the new smallInstance
		smallInstance = smallInstance
	}
	bigInstance, _, err = bigInstance.FoldProve(r1cs, smallInstance, pk_e)
	if err != nil {
		return nil, err
	}
	return bigInstance, nil
}
