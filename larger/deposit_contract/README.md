# Eth2 Deposit Contract

The [Eth2 Deposit Contract](https://github.com/axic/eth2-deposit-contract/blob/master/deposit_contract.sol)
is a small but massively important contract for the Ethereum platform.

It was formally verified by [Runtime Verification](https://runtimeverification.com/blog/end-to-end-formal-verification-of-ethereum-2-0-deposit-smart-contract/),
including the main property that the incremental Merkle tree is equivalent to
the standard one, but it remains an important benchmark for automated tools.

The smt2 file in this directory represents the Horn query that checks the
functional property that the `assert(false)` at the end of function `deposit`
is not reachable.

Note that in order to make the query feasible for the backend solvers,
I changed the expression `if ((size & 1) == 1)` to `if ((size % 2) == 1)`
before asking the SMTChecker to create the Horn query.
This expression is used twice in the contract, once in function
`get_deposit_root` and once in function `deposit`.
The expressions are semantically equivalent even though the compiled bytecode
may be different.