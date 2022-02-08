(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_A_24_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_A_24_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_A_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_1_A_24_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_3_constructor_9_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_4_function_f__23_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |interface_5_C_59_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_6_C_59_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_7_C_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_6_C_59_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_8_constructor_9_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_9_function_f__23_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |summary_10_constructor_58_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_11_function_f__23_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_12_f_22_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int))
(block_11_function_f__23_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _12_1)))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int))
(=> (and (and (block_11_function_f__23_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _12_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_12_f_22_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _12_1))))


(declare-fun |block_13_return_function_f__23_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_12_f_22_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _12_1) (and (= _12_2 expr_20_0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 x_3_2) (and (= x_3_2 expr_18_1) (and (=> true (and (>= expr_18_1 0) (<= expr_18_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_1 expr_17_1) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 x_3_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 (+ expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 1) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_3_1) (and (= _12_1 0) true)))))))))))))))) true) (block_13_return_function_f__23_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2 _12_2))))


(declare-fun |block_14_return_ghost_f_21_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_14_return_ghost_f_21_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2 _12_2) (and (= _12_2 expr_20_0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 x_3_2) (and (= x_3_2 expr_18_1) (and (=> true (and (>= expr_18_1 0) (<= expr_18_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_1 expr_17_1) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 x_3_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 (+ expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 1) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_3_1) (and (= _12_1 0) true)))))))))))))))) true) (block_13_return_function_f__23_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2 _12_2))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_13_return_function_f__23_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _12_1) true) true) (summary_4_function_f__23_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _12_1))))


(declare-fun |block_15_constructor_9_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_16__8_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_0 Int) (_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(block_15_constructor_9_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1)))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_0 Int) (_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_15_constructor_9_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= _5_1 _5_0))) true)) true) (block_16__8_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1))))


(declare-fun |block_17_return_constructor_9_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_0 Int) (_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_16__8_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1) (and (and (>= _5_1 0) (<= _5_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)) true) (block_17_return_constructor_9_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_0 Int) (_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (block_17_return_constructor_9_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1) true) true) (summary_3_constructor_9_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1))))


(declare-fun |contract_initializer_18_A_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_19_A_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_0 Int) (_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= _5_1 _5_0))) (contract_initializer_entry_19_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1))))


(declare-fun |contract_initializer_after_init_20_A_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_0 Int) (_5_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (contract_initializer_entry_19_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 42) true)))) true) (contract_initializer_after_init_20_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_2 _5_1))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (contract_initializer_after_init_20_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1) (and (summary_3_constructor_9_24_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 _5_1 state_2 x_3_2 _5_2) true)) (> error_1 0)) (contract_initializer_18_A_24_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_2 x_3_2 _5_2))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (contract_initializer_after_init_20_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1) (and (= error_1 0) (and (summary_3_constructor_9_24_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 _5_1 state_2 x_3_2 _5_2) true))) true) (contract_initializer_18_A_24_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_2 x_3_2 _5_2))))


(declare-fun |implicit_constructor_entry_21_A_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_3_2 x_3_0))) (and true (= _5_2 _5_0))) (and true (= x_3_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_21_A_24_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_2 x_3_2 _5_2))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (implicit_constructor_entry_21_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_2) (and (contract_initializer_18_A_24_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 _5_2 state_2 x_3_2 _5_3) true)) (> error_1 0)) (summary_constructor_2_A_24_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_2 x_3_2 _5_3))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (implicit_constructor_entry_21_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_2) (and (= error_1 0) (and (contract_initializer_18_A_24_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 _5_2 state_2 x_3_2 _5_3) true))) true) (summary_constructor_2_A_24_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_2 x_3_2 _5_3))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int))
(=> (and (and (summary_constructor_2_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_24_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_22_function_f__23_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_23_f_22_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_22_function_f__23_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _12_1)))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_22_function_f__23_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _12_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_23_f_22_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _12_1))))


(declare-fun |block_24_return_function_f__23_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_23_f_22_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _12_1) (and (= _12_2 expr_20_0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 x_3_2) (and (= x_3_2 expr_18_1) (and (=> true (and (>= expr_18_1 0) (<= expr_18_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_1 expr_17_1) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 x_3_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 (+ expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 1) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_3_1) (and (= _12_1 0) true)))))))))))))))) true) (block_24_return_function_f__23_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2 _12_2))))


(declare-fun |block_25_return_ghost_f_21_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_25_return_ghost_f_21_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2 _12_2) (and (= _12_2 expr_20_0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 x_3_2) (and (= x_3_2 expr_18_1) (and (=> true (and (>= expr_18_1 0) (<= expr_18_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_1 expr_17_1) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 x_3_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 (+ expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 1) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_3_1) (and (= _12_1 0) true)))))))))))))))) true) (block_24_return_function_f__23_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2 _12_2))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_24_return_function_f__23_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _12_1) true) true) (summary_9_function_f__23_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1 _12_1))))


(declare-fun |block_26_constructor_58_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_27__57_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_26_constructor_58_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_26_constructor_58_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_27__57_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_28_return_constructor_58_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_29_constructor_58_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_27__57_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_36_1 (= expr_34_0 expr_35_0)) (and (=> true true) (and (= expr_35_0 42) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 x_3_1) true)))))) (and (not expr_36_1) (= error_1 1))) (block_29_constructor_58_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_29_constructor_58_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_10_constructor_58_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_30_constructor_58_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_27__57_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_42_1 (= expr_40_0 expr_41_0)) (and (=> true true) (and (= expr_41_0 0) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_0 x_3_1) (and (= error_1 error_0) (and (= expr_36_1 (= expr_34_0 expr_35_0)) (and (=> true true) (and (= expr_35_0 42) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 x_3_1) true)))))))))))) (and (not expr_42_1) (= error_2 2))) (block_30_constructor_58_59_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_30_constructor_58_59_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_10_constructor_58_59_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_31_constructor_58_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_27__57_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_48_1 (= expr_46_0 expr_47_0)) (and (=> true true) (and (= expr_47_0 1) (and (=> true (and (>= expr_46_0 0) (<= expr_46_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_46_0 x_3_1) (and (= error_2 error_1) (and (= expr_42_1 (= expr_40_0 expr_41_0)) (and (=> true true) (and (= expr_41_0 0) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_0 x_3_1) (and (= error_1 error_0) (and (= expr_36_1 (= expr_34_0 expr_35_0)) (and (=> true true) (and (= expr_35_0 42) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 x_3_1) true)))))))))))))))))) (and (not expr_48_1) (= error_3 3))) (block_31_constructor_58_59_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_31_constructor_58_59_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_10_constructor_58_59_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_32_constructor_58_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_27__57_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_54_1 (> expr_52_0 expr_53_0)) (and (=> true true) (and (= expr_53_0 2000) (and (=> true (and (>= expr_52_0 0) (<= expr_52_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_52_0 x_3_1) (and (= error_3 error_2) (and (= expr_48_1 (= expr_46_0 expr_47_0)) (and (=> true true) (and (= expr_47_0 1) (and (=> true (and (>= expr_46_0 0) (<= expr_46_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_46_0 x_3_1) (and (= error_2 error_1) (and (= expr_42_1 (= expr_40_0 expr_41_0)) (and (=> true true) (and (= expr_41_0 0) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_0 x_3_1) (and (= error_1 error_0) (and (= expr_36_1 (= expr_34_0 expr_35_0)) (and (=> true true) (and (= expr_35_0 42) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 x_3_1) true)))))))))))))))))))))))) (and (not expr_54_1) (= error_4 4))) (block_32_constructor_58_59_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (block_32_constructor_58_59_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_10_constructor_58_59_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_27__57_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_4 error_3) (and (= expr_54_1 (> expr_52_0 expr_53_0)) (and (=> true true) (and (= expr_53_0 2000) (and (=> true (and (>= expr_52_0 0) (<= expr_52_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_52_0 x_3_1) (and (= error_3 error_2) (and (= expr_48_1 (= expr_46_0 expr_47_0)) (and (=> true true) (and (= expr_47_0 1) (and (=> true (and (>= expr_46_0 0) (<= expr_46_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_46_0 x_3_1) (and (= error_2 error_1) (and (= expr_42_1 (= expr_40_0 expr_41_0)) (and (=> true true) (and (= expr_41_0 0) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_0 x_3_1) (and (= error_1 error_0) (and (= expr_36_1 (= expr_34_0 expr_35_0)) (and (=> true true) (and (= expr_35_0 42) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 x_3_1) true))))))))))))))))))))))))) true) (block_28_return_constructor_58_59_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_28_return_constructor_58_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_10_constructor_58_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_33_C_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_34_C_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_34_C_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_35_C_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_34_C_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_35_C_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_35_C_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_10_constructor_58_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_33_C_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_35_C_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_10_constructor_58_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_33_C_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |block_36_constructor_9_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_37__8_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(block_36_constructor_9_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1)))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_36_constructor_9_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= _5_1 _5_0))) true)) true) (block_37__8_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1))))


(declare-fun |block_38_return_constructor_9_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_37__8_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1) (and (and (>= _5_1 0) (<= _5_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)) true) (block_38_return_constructor_9_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (block_38_return_constructor_9_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1) true) true) (summary_8_constructor_9_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1))))


(declare-fun |contract_initializer_39_A_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_40_A_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= _5_1 _5_0))) (contract_initializer_entry_40_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1))))


(declare-fun |contract_initializer_after_init_41_A_24_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_entry_40_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 42) true)))) true) (contract_initializer_after_init_41_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_2 _5_1))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_41_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1) (and (summary_8_constructor_9_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 _5_1 state_2 x_3_2 _5_2) true)) (> error_1 0)) (contract_initializer_39_A_24_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_2 x_3_2 _5_2))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (contract_initializer_after_init_41_A_24_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_1 x_3_1 _5_1) (and (= error_1 0) (and (summary_8_constructor_9_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 _5_1 state_2 x_3_2 _5_2) true))) true) (contract_initializer_39_A_24_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 _5_0 state_2 x_3_2 _5_2))))


(declare-fun |implicit_constructor_entry_42_C_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_3_2 x_3_0))) true) (and true (= x_3_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_42_C_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |summary_43_function_f__23_59_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (summary_9_function_f__23_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2 _12_2) (summary_43_function_f__23_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2 _12_2))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_42_C_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_43_function_f__23_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2 _12_2) (and true true))) (> error_1 0)) (summary_constructor_7_C_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int))
(=> (and (and (implicit_constructor_entry_42_C_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_39_A_24_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 _5_2 state_3 x_3_3 _5_3) (and (= _5_2 expr_30_0) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 _12_2) (and (= error_1 0) (and (summary_43_function_f__23_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2 _12_2) (and true true)))))))) (> error_2 0)) (summary_constructor_7_C_59_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_3))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (implicit_constructor_entry_42_C_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_33_C_59_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_3_3 state_4 x_3_4) (and (= error_2 0) (and (contract_initializer_39_A_24_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 _5_2 state_3 x_3_3 _5_3) (and (= _5_2 expr_30_0) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 _12_2) (and (= error_1 0) (and (summary_43_function_f__23_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2 _12_2) (and true true)))))))))) (> error_3 0)) (summary_constructor_7_C_59_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_4 x_3_4))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (implicit_constructor_entry_42_C_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_3 0) (and (contract_initializer_33_C_59_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_3_3 state_4 x_3_4) (and (= error_2 0) (and (contract_initializer_39_A_24_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 _5_2 state_3 x_3_3 _5_3) (and (= _5_2 expr_30_0) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 _12_2) (and (= error_1 0) (and (summary_43_function_f__23_59_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2 _12_2) (and true true))))))))))) true) (summary_constructor_7_C_59_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_4 x_3_4))))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (summary_constructor_7_C_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_5_C_59_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> (and (and (summary_constructor_7_C_59_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_5_0)))


(assert
(forall ( (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_5_0 Int) (_5_1 Int) (_5_2 Int) (_5_3 Int) (_5_4 Int) (_5_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_18_1 Int) (expr_20_0 Int) (expr_2_0 Int) (expr_30_0 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_46_0 Int) (expr_47_0 Int) (expr_48_1 Bool) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (t_function_internal_nonpayable$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (x_3_4 Int))
(=> error_target_5_0 false)))
(check-sat)