package smt

import (
	"context"
	"fmt"
	"math/big"

	libcommon "github.com/gateway-fm/cdk-erigon-lib/common"
	"github.com/ledgerwatch/erigon/smt/pkg/utils"
	"github.com/ledgerwatch/erigon/turbo/trie"
	"github.com/status-im/keycard-go/hexutils"
)

// BuildWitness creates a witness from the SMT
func BuildWitness(s *SMT, rd trie.RetainDecider, ctx context.Context) (*trie.Witness, error) {
	operands := make([]trie.WitnessOperator, 0)

	root, err := s.Db.GetLastRoot()
	if err != nil {
		return nil, err
	}

	action := func(prefix []byte, k utils.NodeKey, v utils.NodeValue12) (bool, error) {
		if rd != nil {
			retain := true
			if v.IsFinalNode() {
				prefixLen := len(prefix)
				if prefixLen > 0 {
					retain = rd.Retain(prefix[:prefixLen-1])
				}
			} else {
				retain = rd.Retain(prefix)
			}

			if !retain {
				h := libcommon.BigToHash(k.ToBigInt())
				hNode := trie.OperatorHash{Hash: h}
				operands = append(operands, &hNode)
				return false, nil
			}
		}

		if v.IsFinalNode() {
			actualK, err := s.Db.GetHashKey(k)
			if err != nil {
				return false, err
			}

			keySource, err := s.Db.GetKeySource(actualK)
			if err != nil {
				return false, err
			}

			t, addr, storage, err := utils.DecodeKeySource(keySource)
			if err != nil {
				return false, err
			}

			valHash := v.Get4to8()
			v, err := s.Db.Get(*valHash)
			if err != nil {
				return false, err
			}

			vInBytes := utils.ArrayBigToScalar(utils.BigIntArrayFromNodeValue8(v.GetNodeValue8())).Bytes()
			if t == utils.SC_CODE {
				code, err := s.Db.GetCode(vInBytes)
				if err != nil {
					return false, err
				}

				operands = append(operands, &trie.OperatorCode{Code: code})
			}

			// fmt.Printf("Node hash: %s, Node type: %d, address %x, storage %x, value %x\n", utils.ConvertBigIntToHex(k.ToBigInt()), t, addr, storage, utils.ArrayBigToScalar(value8).Bytes())
			operands = append(operands, &trie.OperatorSMTLeafValue{
				NodeType:   uint8(t),
				Address:    addr.Bytes(),
				StorageKey: storage.Bytes(),
				Value:      vInBytes,
			})
			return false, nil
		}

		var mask uint32
		if !v.Get0to4().IsZero() {
			mask |= 1
		}

		if !v.Get4to8().IsZero() {
			mask |= 2
		}

		operands = append(operands, &trie.OperatorBranch{
			Mask: mask,
		})

		return true, nil
	}

	err = s.Traverse(ctx, root, action)

	return trie.NewWitness(operands), err
}

// func BuildSMTfromWitness builds SMT from witness
func BuildSMTfromWitness(w *trie.Witness) (*SMT, error) {
	// using memdb
	s := NewSMT(nil)

	balanceMap := make(map[string]*big.Int)
	nonceMap := make(map[string]*big.Int)
	contractMap := make(map[string]string)
	storageMap := make(map[string]map[string]string)

	path := make([]int, 0)

	firstNode := true
	NodeChildCountMap := make(map[string]uint32)
	NodesBranchValueMap := make(map[string]uint32)

	type nodeHash struct {
		path []int
		hash libcommon.Hash
	}

	nodeHashes := make([]nodeHash, 0)

	for i, operator := range w.Operators {
		switch op := operator.(type) {
		case *trie.OperatorSMTLeafValue:
			valScaler := big.NewInt(0).SetBytes(op.Value)
			addr := libcommon.BytesToAddress(op.Address)

			switch op.NodeType {
			case utils.KEY_BALANCE:
				balanceMap[addr.String()] = valScaler

			case utils.KEY_NONCE:
				nonceMap[addr.String()] = valScaler

			case utils.SC_STORAGE:
				if _, ok := storageMap[addr.String()]; !ok {
					storageMap[addr.String()] = make(map[string]string)
				}

				stKey := hexutils.BytesToHex(op.StorageKey)
				if len(stKey) > 0 {
					stKey = fmt.Sprintf("0x%s", stKey)
				}

				storageMap[addr.String()][stKey] = valScaler.String()
			}

			path = path[:len(path)-1]
			NodeChildCountMap[intArrayToString(path)] += 1

			for len(path) != 0 && NodeChildCountMap[intArrayToString(path)] == NodesBranchValueMap[intArrayToString(path)] {
				path = path[:len(path)-1]
			}
			if NodeChildCountMap[intArrayToString(path)] < NodesBranchValueMap[intArrayToString(path)] {
				path = append(path, 1)
			}

		case *trie.OperatorCode:
			addr := libcommon.BytesToAddress(w.Operators[i+1].(*trie.OperatorSMTLeafValue).Address)

			code := hexutils.BytesToHex(op.Code)
			if len(code) > 0 {
				s.Db.AddCode(hexutils.HexToBytes(code))
				code = fmt.Sprintf("0x%s", code)
			}

			contractMap[addr.String()] = code

		case *trie.OperatorBranch:
			if firstNode {
				firstNode = false
			} else {
				NodeChildCountMap[intArrayToString(path[:len(path)-1])] += 1
			}

			switch op.Mask {
			case 1:
				NodesBranchValueMap[intArrayToString(path)] = 1
				path = append(path, 0)
			case 2:
				NodesBranchValueMap[intArrayToString(path)] = 1
				path = append(path, 1)
			case 3:
				NodesBranchValueMap[intArrayToString(path)] = 2
				path = append(path, 0)
			}

		case *trie.OperatorHash:
			pathCopy := make([]int, len(path))
			copy(pathCopy, path)
			nodeHashes = append(nodeHashes, nodeHash{path: pathCopy, hash: op.Hash})

			path = path[:len(path)-1]
			NodeChildCountMap[intArrayToString(path)] += 1

			for len(path) != 0 && NodeChildCountMap[intArrayToString(path)] == NodesBranchValueMap[intArrayToString(path)] {
				path = path[:len(path)-1]
			}
			if NodeChildCountMap[intArrayToString(path)] < NodesBranchValueMap[intArrayToString(path)] {
				path = append(path, 1)
			}

		default:
			// Unsupported operator type
			return nil, fmt.Errorf("unsupported operator type: %T", op)
		}
	}

	for _, nodeHash := range nodeHashes {
		_, err := s.InsertHashNode(nodeHash.path, nodeHash.hash.Big())
		if err != nil {
			return nil, err
		}

		_, err = s.Db.GetLastRoot()

		if err != nil {
			return nil, err
		}
	}

	for addr, balance := range balanceMap {
		_, err := s.SetAccountBalance(addr, balance)
		if err != nil {
			return nil, err
		}
	}

	for addr, nonce := range nonceMap {
		_, err := s.SetAccountNonce(addr, nonce)
		if err != nil {
			return nil, err
		}
	}

	for addr, code := range contractMap {
		err := s.SetContractBytecode(addr, code)
		if err != nil {
			return nil, err
		}
	}

	for addr, storage := range storageMap {

		_, err := s.SetContractStorage(addr, storage, nil)
		if err != nil {
			fmt.Println("error : unable to set contract storage", err)
		}
	}

	return s, nil
}

func intArrayToString(a []int) string {
	s := ""
	for _, v := range a {
		s += fmt.Sprintf("%d", v)
	}
	return s
}
