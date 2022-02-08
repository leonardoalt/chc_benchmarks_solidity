(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_22_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_22_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_22_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int))
(=> (= error_0 0) (nondet_interface_1_C_22_0 error_0 this_0 abi_0 crypto_0 state_0 x_5_0 state_0 x_5_0))))


(declare-fun |summary_3_function_f__21_22_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_4_function_f__21_22_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_5_f_20_22_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_7_0 Int) (y_7_1 Int))
(block_4_function_f__21_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_1)))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_4_function_f__21_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_5_1 x_5_0))) (and true (= y_7_1 y_7_0))) true)) true) (block_5_f_20_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_1))))


(declare-fun |block_6_return_function_f__21_22_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_7_function_f__21_22_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_5_f_20_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_1) (and (= expr_15_1 (> expr_13_0 expr_14_0)) (and (=> true true) (and (= expr_14_0 1000) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 y_7_1) (and (= _10_1 0) (and (and (>= y_7_1 0) (<= y_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))) (and (not expr_15_1) (= error_1 1))) (block_7_function_f__21_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_7_0 Int) (y_7_1 Int))
(=> (block_7_function_f__21_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_1) (summary_3_function_f__21_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_5_f_20_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_1) (and (= _10_2 expr_18_0) (and (=> true (and (>= expr_18_0 0) (<= expr_18_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_0 y_7_1) (and (= error_1 error_0) (and (= expr_15_1 (> expr_13_0 expr_14_0)) (and (=> true true) (and (= expr_14_0 1000) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 y_7_1) (and (= _10_1 0) (and (and (>= y_7_1 0) (<= y_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))) true) (block_6_return_function_f__21_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_2))))


(declare-fun |block_8_return_ghost_f_19_22_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_8_return_ghost_f_19_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_2) (and (= _10_2 expr_18_0) (and (=> true (and (>= expr_18_0 0) (<= expr_18_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_0 y_7_1) (and (= error_1 error_0) (and (= expr_15_1 (> expr_13_0 expr_14_0)) (and (=> true true) (and (= expr_14_0 1000) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 y_7_1) (and (= _10_1 0) (and (and (>= y_7_1 0) (<= y_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))) true) (block_6_return_function_f__21_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_2))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (block_6_return_function_f__21_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_1) true) true) (summary_3_function_f__21_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_1 _10_1))))


(declare-fun |contract_initializer_9_C_22_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_10_C_22_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_7_0 Int) (y_7_1 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_5_1 x_5_0))) (contract_initializer_entry_10_C_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_5_0 x_5_1))))


(declare-fun |summary_11_function_f__21_22_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (expr_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (summary_3_function_f__21_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_2 _10_2) (summary_11_function_f__21_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_7_0 state_1 x_5_1 y_7_2 _10_2))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (expr_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (contract_initializer_entry_10_C_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_5_0 x_5_1) (and (summary_11_function_f__21_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_5_1 expr_3_0 state_1 x_5_1 y_7_2 _10_2) (and (=> true true) (and (= expr_3_0 2) (and true true))))) (> error_1 0)) (contract_initializer_9_C_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_5_0 x_5_1))))


(declare-fun |contract_initializer_after_init_12_C_22_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (expr_3_0 Int) (expr_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (contract_initializer_entry_10_C_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_5_0 x_5_1) (and (= x_5_2 expr_4_0) (and (=> true (and (>= expr_4_0 0) (<= expr_4_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_4_0 _10_2) (and (= error_1 0) (and (summary_11_function_f__21_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_5_1 expr_3_0 state_1 x_5_1 y_7_2 _10_2) (and (=> true true) (and (= expr_3_0 2) (and true true))))))))) true) (contract_initializer_after_init_12_C_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_5_0 x_5_2))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (expr_3_0 Int) (expr_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (contract_initializer_after_init_12_C_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_5_0 x_5_1) true) true) (contract_initializer_9_C_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_5_0 x_5_1))))


(declare-fun |implicit_constructor_entry_13_C_22_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (expr_3_0 Int) (expr_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_5_1 x_5_0))) (and true (= x_5_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_13_C_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_5_0 x_5_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (expr_3_0 Int) (expr_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (implicit_constructor_entry_13_C_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_5_0 x_5_1) (and (contract_initializer_9_C_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_5_1 x_5_2) true)) (> error_1 0)) (summary_constructor_2_C_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_5_0 x_5_2))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (expr_3_0 Int) (expr_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (implicit_constructor_entry_13_C_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_5_0 x_5_1) (and (= error_1 0) (and (contract_initializer_9_C_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_5_1 x_5_2) true))) true) (summary_constructor_2_C_22_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_5_0 x_5_2))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (expr_3_0 Int) (expr_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int))
(=> (and (and (summary_constructor_2_C_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_5_0 x_5_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_22_0 this_0 abi_0 crypto_0 state_1 x_5_1))))


(declare-fun |error_target_2_0| () Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (expr_3_0 Int) (expr_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int) (y_7_3 Int))
(=> (and (and (summary_constructor_2_C_22_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_5_0 x_5_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_2_0)))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Bool) (expr_18_0 Int) (expr_3_0 Int) (expr_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_7_0 Int) (y_7_1 Int) (y_7_2 Int) (y_7_3 Int))
(=> error_target_2_0 false)))
(check-sat)