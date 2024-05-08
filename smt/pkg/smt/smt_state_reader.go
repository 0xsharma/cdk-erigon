package smt

import (
	"bytes"
	"context"
	"math/big"

	libcommon "github.com/gateway-fm/cdk-erigon-lib/common"
	"github.com/holiman/uint256"
	"github.com/ledgerwatch/erigon/core/types/accounts"
	"github.com/ledgerwatch/erigon/smt/pkg/utils"
	"github.com/ledgerwatch/erigon/turbo/trie"
	"github.com/ledgerwatch/erigon/zkevm/log"
)

func (s *SMT) ReadAccountData(address libcommon.Address) (*accounts.Account, error) {
	account := accounts.Account{}

	balance, err := s.GetAccountBalance(address)
	if err != nil {
		return nil, err
	}
	account.Balance = *balance

	nonce, err := s.GetAccountNonce(address)
	if err != nil {
		return nil, err
	}
	account.Nonce = nonce.Uint64()

	codeHash, err := s.GetAccountCodeHash(address)
	if err != nil {
		return nil, err
	}
	account.CodeHash = codeHash

	account.Root = libcommon.Hash{}

	return &account, nil
}

func (s *SMT) ReadAccountStorage(address libcommon.Address, incarnation uint64, key *libcommon.Hash) ([]byte, error) {
	return []byte{}, nil
}

func (s *SMT) ReadAccountCode(address libcommon.Address, incarnation uint64, codeHash libcommon.Hash) ([]byte, error) {
	code, err := s.Db.GetCode(codeHash.Bytes())
	if err != nil {
		return []byte{}, err
	}

	return code, nil
}

func (s *SMT) ReadAccountCodeSize(address libcommon.Address, incarnation uint64, codeHash libcommon.Hash) (int, error) {
	valueInBytes, err := s.getValueInBytes(utils.SC_LENGTH, address)
	if err != nil {
		return 0, err
	}

	sizeBig := big.NewInt(0).SetBytes(valueInBytes)

	return int(sizeBig.Int64()), nil
}

func (s *SMT) ReadAccountIncarnation(address libcommon.Address) (uint64, error) {
	return 0, nil
}

func (s *SMT) GetAccountBalance(address libcommon.Address) (*uint256.Int, error) {
	balance := uint256.NewInt(0)

	valueInBytes, err := s.getValueInBytes(utils.KEY_BALANCE, address)
	if err != nil {
		log.Error("error getting balance", "error", err)
		return nil, err
	}
	balance.SetBytes(valueInBytes)

	return balance, nil
}

func (s *SMT) GetAccountNonce(address libcommon.Address) (*uint256.Int, error) {
	nonce := uint256.NewInt(0)

	valueInBytes, err := s.getValueInBytes(utils.KEY_NONCE, address)
	if err != nil {
		log.Error("error getting nonce", "error", err)
		return nil, err
	}
	nonce.SetBytes(valueInBytes)

	return nonce, nil
}

func (s *SMT) GetAccountCodeHash(address libcommon.Address) (libcommon.Hash, error) {
	codeHash := libcommon.Hash{}

	valueInBytes, err := s.getValueInBytes(utils.SC_CODE, address)
	if err != nil {
		log.Error("error getting codehash", "error", err)
		return libcommon.Hash{}, err
	}
	codeHash.SetBytes(valueInBytes)

	return codeHash, nil
}

func (s *SMT) GetAccountStorageRoot(address libcommon.Address) (libcommon.Hash, error) {
	storageTrie := trie.New(libcommon.Hash{})

	storageMap, err := s.getStorageMap(address)
	if err != nil {
		return libcommon.Hash{}, err
	}

	for key, value := range storageMap {
		storageTrie.Update(key[:], value[:])
	}

	rootHash := storageTrie.Hash()

	return rootHash, nil
}

func (s *SMT) getValueInBytes(key int, address libcommon.Address) ([]byte, error) {
	value := []byte{}

	ethAddr := address.String()

	kn, err := utils.Key(ethAddr, key)
	if err != nil {
		return nil, err
	}

	keyPath := kn.GetPath()

	keyPathBytes := make([]byte, 0)
	for _, k := range keyPath {
		keyPathBytes = append(keyPathBytes, byte(k))
	}

	action := func(prefix []byte, k utils.NodeKey, v utils.NodeValue12) (bool, error) {
		if !bytes.HasPrefix(keyPathBytes, prefix) {
			return false, nil
		}

		if v.IsFinalNode() {
			valHash := v.Get4to8()
			v, err := s.Db.Get(*valHash)
			if err != nil {
				return false, err
			}
			vInBytes := utils.ArrayBigToScalar(utils.BigIntArrayFromNodeValue8(v.GetNodeValue8())).Bytes()

			value = vInBytes
			return false, nil
		}

		return true, nil
	}

	root, err := s.Db.GetLastRoot()
	if err != nil {
		return nil, err
	}

	err = s.Traverse(context.Background(), root, action)
	if err != nil {
		return nil, err
	}

	return value, nil
}

func (s *SMT) getStorageMap(address libcommon.Address) (map[libcommon.Hash]libcommon.Hash, error) {
	storageMap := make(map[libcommon.Hash]libcommon.Hash)
	action := func(prefix []byte, k utils.NodeKey, v utils.NodeValue12) (bool, error) {
		if v.IsFinalNode() {
			actualK, err := s.Db.GetHashKey(k)
			if err != nil {
				return false, err
			}

			keySource, err := s.Db.GetKeySource(actualK)
			if err != nil {
				return false, err
			}

			t, addr, storageKey, err := utils.DecodeKeySource(keySource)
			if err != nil {
				return false, err
			}

			if t == utils.SC_STORAGE && addr == address {
				valHash := v.Get4to8()
				v, err := s.Db.Get(*valHash)
				if err != nil {
					return false, err

				}
				vInBytes := utils.ArrayBigToScalar(utils.BigIntArrayFromNodeValue8(v.GetNodeValue8())).Bytes()

				storageMap[storageKey] = libcommon.BytesToHash(vInBytes)
				return true, nil
			}

		}

		return true, nil
	}

	root, err := s.Db.GetLastRoot()
	if err != nil {
		return nil, err
	}

	err = s.Traverse(context.Background(), root, action)
	if err != nil {
		return nil, err
	}

	return storageMap, nil
}
