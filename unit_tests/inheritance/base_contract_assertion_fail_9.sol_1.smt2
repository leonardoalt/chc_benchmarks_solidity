(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_A_30_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_A_30_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_1_A_30_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_3_function_f__21_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_4_function_f__21_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_1_A_30_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_0 0) (summary_4_function_f__21_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_1_A_30_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |summary_5_function_v__29_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_6_B_43_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_7_B_43_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_8_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (= error_1 0) (nondet_interface_7_B_43_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_9_function_f__21_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_10_function_v__29_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_11_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_12_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_7_B_43_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_1 0) (summary_12_function_f__42_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_7_B_43_0 error_2 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |interface_13_C_66_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_14_C_66_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_15_C_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (= error_2 0) (nondet_interface_14_C_66_0 error_2 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_16_function_f__21_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_17_function_v__29_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_18_function_f__42_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_19_function_f__42_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_14_C_66_0 error_2 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_2 0) (summary_19_function_f__42_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_14_C_66_0 error_3 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |summary_20_function_g__56_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_21_function_g__56_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_14_C_66_0 error_3 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_3 0) (summary_21_function_g__56_66_0 error_4 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_14_C_66_0 error_4 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |summary_22_function_v__65_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_23_function_f__21_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_24_f_20_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_23_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_23_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_24_f_20_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_25_return_function_f__21_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_26_function_v__29_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (summary_5_function_v__29_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_26_function_v__29_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_24_f_20_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_26_function_v__29_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_3_function_f__21_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_27_function_f__21_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_24_f_20_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_26_function_v__29_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))) (and (not expr_11_1) (= error_2 1))) (block_27_function_f__21_30_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (block_27_function_f__21_30_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_3_function_f__21_30_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_28_function_f__21_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_24_f_20_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 2) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_2) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_26_function_v__29_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))))))))) (and (not expr_17_1) (= error_3 2))) (block_28_function_f__21_30_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (block_28_function_f__21_30_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_3_function_f__21_30_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_24_f_20_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_3 error_2) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 2) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_2) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_26_function_v__29_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))))))))))) true) (block_25_return_function_f__21_30_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_25_return_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_3_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_29_function_f__21_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_29_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_29_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_3_function_f__21_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_4_function_f__21_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (interface_0_A_30_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_4_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_0_A_30_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_30_function_v__29_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_31_v_28_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_30_function_v__29_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_30_function_v__29_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_31_v_28_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_32_return_function_v__29_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_31_v_28_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_26_1) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 expr_25_0) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 x_2_1) (and (=> true true) (and (= expr_25_0 0) true)))))))) true) (block_32_return_function_v__29_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_32_return_function_v__29_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_5_function_v__29_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_33_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_34_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_34_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_35_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_entry_34_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_35_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_after_init_35_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_33_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_36_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_36_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_36_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_33_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_2_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_36_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_1 0) (and (contract_initializer_33_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))) true) (summary_constructor_2_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (summary_constructor_2_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_30_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_37_function_f__21_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_38_f_20_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_37_function_f__21_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_37_function_f__21_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_38_f_20_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_39_return_function_f__21_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_40_function_v__29_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_10_function_v__29_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_40_function_v__29_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_38_f_20_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_40_function_v__29_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_9_function_f__21_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_41_function_f__21_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_38_f_20_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_40_function_v__29_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))) (and (not expr_11_1) (= error_2 4))) (block_41_function_f__21_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_41_function_f__21_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_9_function_f__21_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_42_function_f__21_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_38_f_20_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 2) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_2) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_40_function_v__29_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))))))))) (and (not expr_17_1) (= error_3 5))) (block_42_function_f__21_43_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_42_function_f__21_43_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_9_function_f__21_43_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_38_f_20_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_3 error_2) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 2) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_2) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_40_function_v__29_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))))))))))) true) (block_39_return_function_f__21_43_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_39_return_function_f__21_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_9_function_f__21_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_43_function_v__29_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_44_v_28_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_43_function_v__29_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_43_function_v__29_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_44_v_28_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_45_return_function_v__29_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_44_v_28_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_26_1) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 expr_25_0) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 x_2_1) (and (=> true true) (and (= expr_25_0 0) true)))))))) true) (block_45_return_function_v__29_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_45_return_function_v__29_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_10_function_v__29_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_46_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_47_f_41_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_46_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_46_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_47_f_41_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_48_return_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_49_function_f__21_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_9_function_f__21_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_49_function_f__21_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_47_f_41_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_49_function_f__21_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_11_function_f__42_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_47_f_41_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_49_function_f__21_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (block_48_return_function_f__42_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_48_return_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_11_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_50_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_50_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_50_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_11_function_f__42_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_6_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_6_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_6_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_6_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_12_function_f__42_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_6_B_43_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_12_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_6_B_43_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |contract_initializer_51_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_52_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_52_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_53_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_52_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_53_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_53_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_51_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_54_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_55_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_55_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_56_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_55_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_56_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_56_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_54_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_57_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_57_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_57_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_54_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_8_B_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_57_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_51_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_54_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))) (> error_2 0)) (summary_constructor_8_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_2_0 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_57_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_2 0) (and (contract_initializer_51_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_54_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))))) true) (summary_constructor_8_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_2_0 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (summary_constructor_8_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_6_B_43_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_58_function_f__21_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_59_f_20_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_58_function_f__21_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_58_function_f__21_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_59_f_20_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_60_return_function_f__21_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_61_function_v__65_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_22_function_v__65_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_61_function_v__65_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_59_f_20_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_61_function_v__65_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_16_function_f__21_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_62_function_f__21_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_59_f_20_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_61_function_v__65_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))) (and (not expr_11_1) (= error_2 7))) (block_62_function_f__21_66_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_62_function_f__21_66_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_16_function_f__21_66_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_63_function_f__21_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_59_f_20_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 2) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_2) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_61_function_v__65_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))))))))) (and (not expr_17_1) (= error_3 8))) (block_63_function_f__21_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_63_function_f__21_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_16_function_f__21_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_59_f_20_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_3 error_2) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 2) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_2) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_61_function_v__65_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))))))))))) true) (block_60_return_function_f__21_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_60_return_function_f__21_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_16_function_f__21_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_64_function_v__29_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_65_v_28_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_64_function_v__29_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_64_function_v__29_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_65_v_28_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_66_return_function_v__29_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_65_v_28_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_26_1) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 expr_25_0) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 x_2_1) (and (=> true true) (and (= expr_25_0 0) true)))))))) true) (block_66_return_function_v__29_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_66_return_function_v__29_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_17_function_v__29_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_67_function_f__42_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_68_f_41_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_67_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_67_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_68_f_41_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_69_return_function_f__42_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_70_function_f__21_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_16_function_f__21_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_70_function_f__21_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_68_f_41_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_70_function_f__21_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_18_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_68_f_41_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_70_function_f__21_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (block_69_return_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_69_return_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_18_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_71_function_f__42_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_71_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_71_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_18_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_9_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_9_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_9_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_9_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_19_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_13_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_19_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_13_C_66_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_72_function_g__56_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_73_g_55_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_72_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_72_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_73_g_55_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_74_return_function_g__56_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_75_function_f__42_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_18_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3) (summary_75_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_73_g_55_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_75_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_2 state_2 x_2_3) (and (= x_2_2 expr_50_1) (and (=> true (and (>= expr_50_1 0) (<= expr_50_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_1 expr_49_0) (and (=> true (and (>= expr_48_0 0) (<= expr_48_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_48_0 x_2_1) (and (=> true true) (and (= expr_49_0 1) true))))))))) (> error_1 0)) (summary_20_function_g__56_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_73_g_55_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_75_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_2 state_2 x_2_3) (and (= x_2_2 expr_50_1) (and (=> true (and (>= expr_50_1 0) (<= expr_50_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_1 expr_49_0) (and (=> true (and (>= expr_48_0 0) (<= expr_48_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_48_0 x_2_1) (and (=> true true) (and (= expr_49_0 1) true)))))))))) true) (block_74_return_function_g__56_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_74_return_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_20_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_76_function_g__56_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_76_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_76_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_20_function_g__56_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_10_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_10_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_10_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_10_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_21_function_g__56_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_13_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_21_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_13_C_66_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_77_function_v__65_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_78_v_64_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_77_function_v__65_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_77_function_v__65_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_78_v_64_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_79_return_function_v__65_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_78_v_64_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_62_1) (and (=> true (and (>= expr_62_1 0) (<= expr_62_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_62_1 expr_61_0) (and (=> true (and (>= expr_60_0 0) (<= expr_60_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_60_0 x_2_1) (and (=> true true) (and (= expr_61_0 2) true)))))))) true) (block_79_return_function_v__65_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_79_return_function_v__65_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_22_function_v__65_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_80_C_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_81_C_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_81_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_82_C_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_81_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_82_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_82_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_80_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_83_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_84_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_84_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_85_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_84_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_85_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_85_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_83_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_86_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_87_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_87_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_88_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_87_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_88_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_88_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_86_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_89_C_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_89_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_89_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_86_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_15_C_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_89_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_83_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_86_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))) (> error_2 0)) (summary_constructor_15_C_66_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_2_0 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (implicit_constructor_entry_89_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_80_C_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 x_2_3 x_2_4) (and (= error_2 0) (and (contract_initializer_83_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_86_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))))) (> error_3 0)) (summary_constructor_15_C_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 x_2_0 x_2_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (implicit_constructor_entry_89_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_3 0) (and (contract_initializer_80_C_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 x_2_3 x_2_4) (and (= error_2 0) (and (contract_initializer_83_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_86_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))))))) true) (summary_constructor_15_C_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 x_2_0 x_2_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (summary_constructor_15_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_13_C_66_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |error_target_11_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_0_A_30_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_4_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 1))) error_target_11_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_6_B_43_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_12_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 1))) error_target_11_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_13_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_19_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 1))) error_target_11_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_13_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_21_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 1))) error_target_11_0)))


(declare-fun |error_target_12_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_0_A_30_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_4_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 2))) error_target_12_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_6_B_43_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_12_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 2))) error_target_12_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_13_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_19_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 2))) error_target_12_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_13_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_21_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 2))) error_target_12_0)))


(declare-fun |error_target_13_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_0_A_30_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_4_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 4))) error_target_13_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_6_B_43_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_12_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 4))) error_target_13_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_13_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_19_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 4))) error_target_13_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_13_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_21_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 4))) error_target_13_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_10_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> error_target_13_0 false)))
(check-sat)