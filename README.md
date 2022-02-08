# Solidity CHC Benchmarks

This repo contains CHC benchmarks from 2 sources:

- [Solidity's SMTChecker unit tests](https://github.com/ethereum/solidity/tree/develop/test/libsolidity/smtCheckerTests), in the `unit_tests` directory.
- Larger instances, such as from the [Eth2 Deposit Contract](https://github.com/axic/eth2-deposit-contract/blob/master/deposit_contract.sol)
  and [OpenZeppelin's ERC777 implementation](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/token/ERC777/ERC777.sol), in the `large` directory.

The `unit_tests` directory is further classified into the test focus, whereas
the `large` directory is separated by the application where the benchmark came
from.

The directory `no_adts` contains the same benchmarks/structure as this, with
`unit_tests` and `larger`, where each benchmark was transformed using
https://github.com/leonardoalt/adt_transform/ to remove ADTs.
A benchmark in the `no_adts` directory named `a_no_adts.smt2` has an equivalent
one in this directory named `a.smt2`.
Benchmarks with ADTs that could not be transformed due to a limitation in the
ADT transform tool do not have a correspondent one without ADTs.