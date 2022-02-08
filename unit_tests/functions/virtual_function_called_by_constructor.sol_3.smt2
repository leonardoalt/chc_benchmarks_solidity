(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_A_34_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_A_34_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_A_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_1_A_34_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_3_function_v__10_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_4_constructor_17_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_5_function_i__33_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_6_function_i__33_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_1_A_34_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_0 0) (summary_6_function_i__33_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_1_A_34_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |interface_7_C_63_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_8_C_63_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_9_C_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (= error_1 0) (nondet_interface_8_C_63_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_10_function_v__10_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_11_constructor_17_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_12_function_i__33_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_13_function_v__45_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_14_function_i__62_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_15_function_i__62_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_8_C_63_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_1 0) (summary_15_function_i__62_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_8_C_63_0 error_2 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_16_function_v__10_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_17_v_9_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_16_function_v__10_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_16_function_v__10_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_17_v_9_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_18_return_function_v__10_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_17_v_9_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 x_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_18_return_function_v__10_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_18_return_function_v__10_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_3_function_v__10_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_19_function_i__33_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_20_i_32_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_19_function_i__33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_19_function_i__33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_20_i_32_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_21_return_function_i__33_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_22_function_i__33_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_20_i_32_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_23_1 (= expr_21_0 expr_22_0)) (and (=> true true) (and (= expr_22_0 2) (and (=> true (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 x_2_1) true)))))) (and (not expr_23_1) (= error_1 1))) (block_22_function_i__33_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (block_22_function_i__33_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_5_function_i__33_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_23_function_i__33_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_20_i_32_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 10) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_2_1) (and (= error_1 error_0) (and (= expr_23_1 (= expr_21_0 expr_22_0)) (and (=> true true) (and (= expr_22_0 2) (and (=> true (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 x_2_1) true)))))))))))) (and (not expr_29_1) (= error_2 2))) (block_23_function_i__33_34_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (block_23_function_i__33_34_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_5_function_i__33_34_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_20_i_32_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_2 error_1) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 10) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_2_1) (and (= error_1 error_0) (and (= expr_23_1 (= expr_21_0 expr_22_0)) (and (=> true true) (and (= expr_22_0 2) (and (=> true (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 x_2_1) true))))))))))))) true) (block_21_return_function_i__33_34_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_21_return_function_i__33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_5_function_i__33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_24_function_i__33_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_24_function_i__33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_24_function_i__33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_5_function_i__33_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3853139288)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 229)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 170)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 61)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 88)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_6_function_i__33_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (interface_0_A_34_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_6_function_i__33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_0_A_34_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_25_constructor_17_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_26__16_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_25_constructor_17_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_25_constructor_17_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_26__16_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_27_return_constructor_17_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_28_function_v__10_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (summary_3_function_v__10_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_28_function_v__10_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_26__16_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_28_function_v__10_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_4_constructor_17_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_26__16_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_28_function_v__10_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (block_27_return_constructor_17_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_27_return_constructor_17_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_4_constructor_17_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_29_A_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_30_A_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) (contract_initializer_entry_30_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_after_init_31_A_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_entry_30_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (contract_initializer_after_init_31_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_after_init_31_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_4_constructor_17_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (contract_initializer_29_A_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_after_init_31_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_4_constructor_17_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (contract_initializer_29_A_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |implicit_constructor_entry_32_A_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_2_2 x_2_0))) true) (and true (= x_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_32_A_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_32_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (contract_initializer_29_A_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_constructor_2_A_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_32_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (contract_initializer_29_A_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (summary_constructor_2_A_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (summary_constructor_2_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_34_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_33_function_v__10_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_34_v_9_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_33_function_v__10_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_33_function_v__10_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_34_v_9_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_35_return_function_v__10_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_34_v_9_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 x_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_35_return_function_v__10_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_35_return_function_v__10_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_10_function_v__10_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_36_function_i__33_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_37_i_32_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_36_function_i__33_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_36_function_i__33_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_37_i_32_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_38_return_function_i__33_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_39_function_i__33_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_37_i_32_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_23_1 (= expr_21_0 expr_22_0)) (and (=> true true) (and (= expr_22_0 2) (and (=> true (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 x_2_1) true)))))) (and (not expr_23_1) (= error_1 4))) (block_39_function_i__33_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_39_function_i__33_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_12_function_i__33_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_40_function_i__33_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_37_i_32_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 10) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_2_1) (and (= error_1 error_0) (and (= expr_23_1 (= expr_21_0 expr_22_0)) (and (=> true true) (and (= expr_22_0 2) (and (=> true (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 x_2_1) true)))))))))))) (and (not expr_29_1) (= error_2 5))) (block_40_function_i__33_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_40_function_i__33_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_12_function_i__33_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_37_i_32_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_2 error_1) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 10) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_2_1) (and (= error_1 error_0) (and (= expr_23_1 (= expr_21_0 expr_22_0)) (and (=> true true) (and (= expr_22_0 2) (and (=> true (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 x_2_1) true))))))))))))) true) (block_38_return_function_i__33_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_38_return_function_i__33_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_12_function_i__33_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_41_function_v__45_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_42_v_44_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_41_function_v__45_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_41_function_v__45_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_42_v_44_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_43_return_function_v__45_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_42_v_44_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_42_1) (and (=> true (and (>= expr_42_1 0) (<= expr_42_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_42_1 expr_41_0) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_0 x_2_1) (and (=> true true) (and (= expr_41_0 10) true)))))))) true) (block_43_return_function_v__45_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_43_return_function_v__45_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_13_function_v__45_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_44_function_i__62_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_45_i_61_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_44_function_i__62_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_44_function_i__62_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_45_i_61_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_46_return_function_i__62_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_47_function_i__62_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_45_i_61_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_52_1 (= expr_50_0 expr_51_0)) (and (=> true true) (and (= expr_51_0 10) (and (=> true (and (>= expr_50_0 0) (<= expr_50_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_0 x_2_1) true)))))) (and (not expr_52_1) (= error_1 6))) (block_47_function_i__62_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_47_function_i__62_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_14_function_i__62_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_48_function_i__62_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_45_i_61_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_58_1 (= expr_56_0 expr_57_0)) (and (=> true true) (and (= expr_57_0 2) (and (=> true (and (>= expr_56_0 0) (<= expr_56_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_56_0 x_2_1) (and (= error_1 error_0) (and (= expr_52_1 (= expr_50_0 expr_51_0)) (and (=> true true) (and (= expr_51_0 10) (and (=> true (and (>= expr_50_0 0) (<= expr_50_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_0 x_2_1) true)))))))))))) (and (not expr_58_1) (= error_2 7))) (block_48_function_i__62_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_48_function_i__62_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_14_function_i__62_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_45_i_61_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_2 error_1) (and (= expr_58_1 (= expr_56_0 expr_57_0)) (and (=> true true) (and (= expr_57_0 2) (and (=> true (and (>= expr_56_0 0) (<= expr_56_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_56_0 x_2_1) (and (= error_1 error_0) (and (= expr_52_1 (= expr_50_0 expr_51_0)) (and (=> true true) (and (= expr_51_0 10) (and (=> true (and (>= expr_50_0 0) (<= expr_50_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_0 x_2_1) true))))))))))))) true) (block_46_return_function_i__62_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_46_return_function_i__62_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_14_function_i__62_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_49_function_i__62_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_49_function_i__62_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_49_function_i__62_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_14_function_i__62_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_8_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_8_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_8_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_8_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3853139288)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 229)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 170)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 61)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 88)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_15_function_i__62_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_7_C_63_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_15_function_i__62_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_7_C_63_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |contract_initializer_50_C_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_51_C_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_51_C_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_52_C_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_51_C_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_52_C_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_52_C_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_50_C_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |block_53_constructor_17_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_54__16_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_53_constructor_17_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_53_constructor_17_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_54__16_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_55_return_constructor_17_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_56_function_v__45_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_13_function_v__45_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_56_function_v__45_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_54__16_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_56_function_v__45_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_11_constructor_17_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_54__16_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_56_function_v__45_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (block_55_return_constructor_17_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_55_return_constructor_17_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_11_constructor_17_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_57_A_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_58_A_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) (contract_initializer_entry_58_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_after_init_59_A_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_58_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (contract_initializer_after_init_59_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_59_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_11_constructor_17_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (contract_initializer_57_A_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_59_A_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_11_constructor_17_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (contract_initializer_57_A_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |implicit_constructor_entry_60_C_63_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_2_2 x_2_0))) (and true (= x_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_60_C_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_60_C_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_57_A_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_constructor_9_C_63_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_60_C_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_50_C_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_57_A_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))) (> error_2 0)) (summary_constructor_9_C_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_2_0 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_60_C_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_2 0) (and (contract_initializer_50_C_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_57_A_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))) true) (summary_constructor_9_C_63_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_2_0 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (summary_constructor_9_C_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_7_C_63_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |error_target_9_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_0_A_34_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_6_function_i__33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 1))) error_target_9_0)))


(declare-fun |error_target_10_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_0_A_34_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_6_function_i__33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 2))) error_target_10_0)))


(declare-fun |error_target_11_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_0_A_34_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_6_function_i__33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 4))) error_target_11_0)))


(declare-fun |error_target_12_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_0_A_34_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_6_function_i__33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 5))) error_target_12_0)))


(declare-fun |error_target_13_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_7_C_63_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_15_function_i__62_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 6))) error_target_13_0)))


(declare-fun |error_target_14_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_7_C_63_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_15_function_i__62_63_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 7))) error_target_14_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_14_1 |tuple()|) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Int) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (funds_3_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> error_target_14_0 false)))
(check-sat)