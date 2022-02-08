(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_64_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_64_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_64_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_test__63_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_4_function_test__63_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_64_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_C_64_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_5_function_test__63_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_6_test_62_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(block_5_function_test__63_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_5_function_test__63_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_6_test_62_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1))))


(declare-fun |block_7_return_function_test__63_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_8_if_header_test_30_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_9_if_true_test_29_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_10_test_62_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_6_test_62_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (= x_4_1 0) true)) true) (block_8_if_header_test_30_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1))))


(declare-fun |block_11_function_test__63_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_8_if_header_test_30_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (=> true true) (and (= expr_23_0 7) (and (=> true true) (and (= expr_22_0 57896044618658097711785492504343953926634992332820282019728792003956564819968) (and (=> true true) (and (= expr_19_0 57896044618658097711785492504343953926634992332820282019728792003956564819968) (and true (and (=> true true) (and (= expr_15_0 2) true)))))))))) (and (= expr_23_0 0) (= error_1 1))) (block_11_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (block_11_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (summary_3_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_8_if_header_test_30_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (= expr_25_1 (not (= expr_15_0 expr_24_1))) (and (=> true (and (>= expr_24_1 0) (<= expr_24_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_1 (mod (+ expr_19_0 expr_22_0) expr_23_0)) (and (= error_1 error_0) (and (=> true true) (and (= expr_23_0 7) (and (=> true true) (and (= expr_22_0 57896044618658097711785492504343953926634992332820282019728792003956564819968) (and (=> true true) (and (= expr_19_0 57896044618658097711785492504343953926634992332820282019728792003956564819968) (and true (and (=> true true) (and (= expr_15_0 2) true)))))))))))))) expr_25_1) (block_9_if_true_test_29_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_8_if_header_test_30_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (= expr_25_1 (not (= expr_15_0 expr_24_1))) (and (=> true (and (>= expr_24_1 0) (<= expr_24_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_1 (mod (+ expr_19_0 expr_22_0) expr_23_0)) (and (= error_1 error_0) (and (=> true true) (and (= expr_23_0 7) (and (=> true true) (and (= expr_22_0 57896044618658097711785492504343953926634992332820282019728792003956564819968) (and (=> true true) (and (= expr_19_0 57896044618658097711785492504343953926634992332820282019728792003956564819968) (and true (and (=> true true) (and (= expr_15_0 2) true)))))))))))))) (not expr_25_1)) (block_10_test_62_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_9_if_true_test_29_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (= x_4_2 expr_28_1) (and (=> true (and (>= expr_28_1 0) (<= expr_28_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_1 expr_27_0) (and (=> true (and (>= expr_26_0 0) (<= expr_26_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_0 x_4_1) (and (=> true true) (and (= expr_27_0 1) true)))))))) true) (block_10_test_62_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_2))))


(declare-fun |block_12_if_header_test_55_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_13_if_true_test_54_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_14_test_62_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_10_test_62_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) true) true) (block_12_if_header_test_55_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1))))


(declare-fun |block_15_function_test__63_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_12_if_header_test_55_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (=> true true) (and (= expr_48_0 7) (and (=> true true) (and (= expr_47_0 57896044618658097711785492504343953926634992332820282019728792003956564819968) (and (=> true true) (and (= expr_44_0 57896044618658097711785492504343953926634992332820282019728792003956564819968) (and (=> true true) (and (= expr_40_0 2) true))))))))) (and (= expr_48_0 0) (= error_1 2))) (block_15_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (block_15_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (summary_3_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_12_if_header_test_55_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (= expr_50_1 (not (= expr_40_0 expr_49_1))) (and (=> true (and (>= expr_49_1 0) (<= expr_49_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_49_1 (mod (+ expr_44_0 expr_47_0) expr_48_0)) (and (= error_1 error_0) (and (=> true true) (and (= expr_48_0 7) (and (=> true true) (and (= expr_47_0 57896044618658097711785492504343953926634992332820282019728792003956564819968) (and (=> true true) (and (= expr_44_0 57896044618658097711785492504343953926634992332820282019728792003956564819968) (and (=> true true) (and (= expr_40_0 2) true))))))))))))) expr_50_1) (block_13_if_true_test_54_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_12_if_header_test_55_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (= expr_50_1 (not (= expr_40_0 expr_49_1))) (and (=> true (and (>= expr_49_1 0) (<= expr_49_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_49_1 (mod (+ expr_44_0 expr_47_0) expr_48_0)) (and (= error_1 error_0) (and (=> true true) (and (= expr_48_0 7) (and (=> true true) (and (= expr_47_0 57896044618658097711785492504343953926634992332820282019728792003956564819968) (and (=> true true) (and (= expr_44_0 57896044618658097711785492504343953926634992332820282019728792003956564819968) (and (=> true true) (and (= expr_40_0 2) true))))))))))))) (not expr_50_1)) (block_14_test_62_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_13_if_true_test_54_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (= x_4_2 expr_53_1) (and (=> true (and (>= expr_53_1 0) (<= expr_53_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_53_1 expr_52_0) (and (=> true (and (>= expr_51_0 0) (<= expr_51_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_51_0 x_4_1) (and (=> true true) (and (= expr_52_0 2) true)))))))) true) (block_14_test_62_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_2))))


(declare-fun |block_16_function_test__63_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_14_test_62_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (= expr_59_1 (= expr_57_0 expr_58_0)) (and (=> true true) (and (= expr_58_0 0) (and (=> true (and (>= expr_57_0 0) (<= expr_57_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_57_0 x_4_1) true)))))) (and (not expr_59_1) (= error_1 3))) (block_16_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (block_16_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (summary_3_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_14_test_62_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (= error_1 error_0) (and (= expr_59_1 (= expr_57_0 expr_58_0)) (and (=> true true) (and (= expr_58_0 0) (and (=> true (and (>= expr_57_0 0) (<= expr_57_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_57_0 x_4_1) true))))))) true) (block_7_return_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_7_return_function_test__63_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) true) true) (summary_3_function_test__63_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_17_function_test__63_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(block_17_function_test__63_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_17_function_test__63_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_4_1) (and (summary_3_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_4_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_4_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_4_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_4_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 4171824493)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 248)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 168)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 253)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 109)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_4_function_test__63_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (interface_0_C_64_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_test__63_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_0_C_64_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_18_C_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_19_C_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_19_C_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_20_C_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_entry_19_C_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_20_C_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_20_C_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_18_C_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_21_C_64_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_21_C_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (implicit_constructor_entry_21_C_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_18_C_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (implicit_constructor_entry_21_C_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_18_C_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_64_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (summary_constructor_2_C_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_64_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (interface_0_C_64_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_test__63_64_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 1))) error_target_5_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_15_0 Int) (expr_19_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_40_0 Int) (expr_44_0 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Int) (expr_50_1 Bool) (expr_51_0 Int) (expr_52_0 Int) (expr_53_1 Int) (expr_57_0 Int) (expr_58_0 Int) (expr_59_1 Bool) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_addmod_pure$_t_uint256_$_t_uint256_$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> error_target_5_0 false)))
(check-sat)