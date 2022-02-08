(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_41_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_41_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_41_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_test__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_4_function_test__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_41_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_test__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_C_41_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_5_function_branches__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_6_function_test__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_7_test_19_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_25_1 Int) (a_22_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_6_function_test__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (_25_1 Int) (a_22_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_function_test__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_7_test_19_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_8_return_function_test__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_9_function_branches__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_25_1 Int) (_25_2 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_5_function_branches__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_2 _25_2) (summary_9_function_branches__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_2 _25_2))))


(assert
(forall ( (_25_1 Int) (_25_2 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_test_19_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_9_function_branches__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 expr_5_0 state_1 a_22_2 _25_2) (and (=> true true) (and (= expr_5_0 0) (and true true))))) (> error_1 0)) (summary_3_function_test__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_10_function_test__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_25_1 Int) (_25_2 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_test_19_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_8_1 (= expr_6_0 expr_7_0)) (and (=> true true) (and (= expr_7_0 0) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 _25_2) (and (= error_1 0) (and (summary_9_function_branches__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 expr_5_0 state_1 a_22_2 _25_2) (and (=> true true) (and (= expr_5_0 0) (and true true))))))))))) (and (not expr_8_1) (= error_2 1))) (block_10_function_test__20_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_25_1 Int) (_25_2 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (block_10_function_test__20_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_3_function_test__20_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |summary_11_function_branches__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_5_function_branches__40_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_3 _25_3) (summary_11_function_branches__40_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_3 _25_3))))


(assert
(forall ( (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_test_19_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_11_function_branches__40_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 expr_13_0 state_1 a_22_3 _25_3) (and (=> true true) (and (= expr_13_0 1) (and (= error_2 error_1) (and (= expr_8_1 (= expr_6_0 expr_7_0)) (and (=> true true) (and (= expr_7_0 0) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 _25_2) (and (= error_1 0) (and (summary_9_function_branches__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 expr_5_0 state_1 a_22_2 _25_2) (and (=> true true) (and (= expr_5_0 0) (and true true))))))))))))))) (> error_3 0)) (summary_3_function_test__20_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_12_function_test__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_test_19_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_16_1 (= expr_14_0 expr_15_0)) (and (=> true true) (and (= expr_15_0 42) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 _25_3) (and (= error_3 0) (and (summary_11_function_branches__40_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 expr_13_0 state_1 a_22_3 _25_3) (and (=> true true) (and (= expr_13_0 1) (and (= error_2 error_1) (and (= expr_8_1 (= expr_6_0 expr_7_0)) (and (=> true true) (and (= expr_7_0 0) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 _25_2) (and (= error_1 0) (and (summary_9_function_branches__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 expr_5_0 state_1 a_22_2 _25_2) (and (=> true true) (and (= expr_5_0 0) (and true true))))))))))))))))))))) (and (not expr_16_1) (= error_4 2))) (block_12_function_test__20_41_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (block_12_function_test__20_41_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_3_function_test__20_41_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_test_19_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_4 error_3) (and (= expr_16_1 (= expr_14_0 expr_15_0)) (and (=> true true) (and (= expr_15_0 42) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 _25_3) (and (= error_3 0) (and (summary_11_function_branches__40_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 expr_13_0 state_1 a_22_3 _25_3) (and (=> true true) (and (= expr_13_0 1) (and (= error_2 error_1) (and (= expr_8_1 (= expr_6_0 expr_7_0)) (and (=> true true) (and (= expr_7_0 0) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 _25_2) (and (= error_1 0) (and (summary_9_function_branches__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 expr_5_0 state_1 a_22_2 _25_2) (and (=> true true) (and (= expr_5_0 0) (and true true)))))))))))))))))))))) true) (block_8_return_function_test__20_41_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_return_function_test__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_3_function_test__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_13_function_test__20_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(block_13_function_test__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_function_test__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_3_function_test__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 4171824493)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 248)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 168)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 253)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 109)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_4_function_test__20_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_41_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_test__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_0_C_41_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_14_function_branches__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_15_branches_39_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(block_14_function_branches__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1)))


(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_function_branches__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= a_22_1 a_22_0))) true)) true) (block_15_branches_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1))))


(declare-fun |block_16_return_function_branches__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_17_if_header_branches_36_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_18_if_true_branches_32_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_19_if_false_branches_35_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_20_branches_39_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_branches_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1) (and (= _25_1 0) (and (and (>= a_22_1 0) (<= a_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))) true) (block_17_if_header_branches_36_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1))))


(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_17_if_header_branches_36_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 0) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 a_22_1) true)))))) expr_29_1) (block_18_if_true_branches_32_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1))))


(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_17_if_header_branches_36_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 0) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 a_22_1) true)))))) (not expr_29_1)) (block_19_if_false_branches_35_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1))))


(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_18_if_true_branches_32_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1) (and (= _25_2 expr_30_0) (and (=> true true) (and (= expr_30_0 0) true)))) true) (block_16_return_function_branches__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_2))))


(declare-fun |block_21_return_ghost_branches_31_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_21_return_ghost_branches_31_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_2) (and (= _25_2 expr_30_0) (and (=> true true) (and (= expr_30_0 0) true)))) true) (block_20_branches_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_2))))


(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_19_if_false_branches_35_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1) (and (= _25_2 expr_33_0) (and (=> true true) (and (= expr_33_0 42) true)))) true) (block_16_return_function_branches__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_2))))


(declare-fun |block_22_return_ghost_branches_34_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_22_return_ghost_branches_34_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_2) (and (= _25_2 expr_33_0) (and (=> true true) (and (= expr_33_0 42) true)))) true) (block_20_branches_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_2))))


(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_37_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_20_branches_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1) (and (= _25_2 expr_37_0) (and (=> true true) (and (= expr_37_0 1) true)))) true) (block_16_return_function_branches__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_2))))


(declare-fun |block_23_return_ghost_branches_38_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_37_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_23_return_ghost_branches_38_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_2) (and (= _25_2 expr_37_0) (and (=> true true) (and (= expr_37_0 1) true)))) true) (block_16_return_function_branches__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_2))))


(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_37_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_return_function_branches__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1) true) true) (summary_5_function_branches__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_22_0 state_1 a_22_1 _25_1))))


(declare-fun |contract_initializer_24_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_25_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_37_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_25_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_26_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_37_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_25_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_26_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_37_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_26_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_24_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_27_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_37_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_27_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_37_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_27_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_24_C_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_37_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_27_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_24_C_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_37_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_41_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_37_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_41_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_test__20_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 1))) error_target_4_0)))


(assert
(forall ( (_25_0 Int) (_25_1 Int) (_25_2 Int) (_25_3 Int) (a_22_0 Int) (a_22_1 Int) (a_22_2 Int) (a_22_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_13_0 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_30_0 Int) (expr_33_0 Int) (expr_37_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_4_0 false)))
(check-sat)