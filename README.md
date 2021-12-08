# Solidity CHC Benchmarks

This repo contains CHC benchmarks from 2 sources:

- [Solidity's SMTChecker unit tests](https://github.com/ethereum/solidity/tree/develop/test/libsolidity/smtCheckerTests), in the `unit_tests` directory.
- Larger instances, such as from the [Eth2 Deposit Contract](https://github.com/axic/eth2-deposit-contract/blob/master/deposit_contract.sol)
  and [OpenZeppelin's ERC777 implementation](https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/token/ERC777/ERC777.sol), in the `large` directory.

The `unit_tests` directory is further classified into the test focus, whereas
the `large` directory is separated by the application where the benchmark came
from.