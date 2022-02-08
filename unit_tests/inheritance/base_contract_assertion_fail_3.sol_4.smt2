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
(declare-fun |summary_4_function_v__29_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_5_B_43_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_6_B_43_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_7_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_6_B_43_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_8_function_f__21_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_9_function_v__29_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_10_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_11_C_66_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_12_C_66_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_13_C_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_12_C_66_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_14_function_f__21_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_15_function_v__29_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_16_function_f__42_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_17_function_g__56_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_18_function_g__56_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_12_C_66_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_0 0) (summary_18_function_g__56_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_12_C_66_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |summary_19_function_v__65_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_20_function_f__21_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_21_f_20_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_20_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_20_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_21_f_20_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_22_return_function_f__21_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_23_function_v__29_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (summary_4_function_v__29_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_23_function_v__29_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_21_f_20_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_23_function_v__29_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_3_function_f__21_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_24_function_f__21_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_21_f_20_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_23_function_v__29_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))) (and (not expr_11_1) (= error_2 1))) (block_24_function_f__21_30_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (block_24_function_f__21_30_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_3_function_f__21_30_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_25_function_f__21_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_21_f_20_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 2) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_2) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_23_function_v__29_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))))))))) (and (not expr_17_1) (= error_3 2))) (block_25_function_f__21_30_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (block_25_function_f__21_30_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_3_function_f__21_30_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_21_f_20_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_3 error_2) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 2) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_2) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_23_function_v__29_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))))))))))) true) (block_22_return_function_f__21_30_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_22_return_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_3_function_f__21_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_26_function_v__29_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_27_v_28_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_26_function_v__29_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_26_function_v__29_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_27_v_28_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_28_return_function_v__29_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_27_v_28_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_26_1) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 expr_25_0) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 x_2_1) (and (=> true true) (and (= expr_25_0 0) true)))))))) true) (block_28_return_function_v__29_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_28_return_function_v__29_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_4_function_v__29_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_29_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_30_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_30_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_31_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_entry_30_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_31_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_after_init_31_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_29_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_32_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_32_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_32_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_29_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_2_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_32_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_1 0) (and (contract_initializer_29_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))) true) (summary_constructor_2_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (summary_constructor_2_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_30_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_33_function_f__21_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_34_f_20_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_33_function_f__21_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_33_function_f__21_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_34_f_20_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_35_return_function_f__21_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_36_function_v__29_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_9_function_v__29_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_36_function_v__29_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_34_f_20_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_36_function_v__29_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_8_function_f__21_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_37_function_f__21_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_34_f_20_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_36_function_v__29_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))) (and (not expr_11_1) (= error_2 3))) (block_37_function_f__21_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_37_function_f__21_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_8_function_f__21_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_38_function_f__21_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_34_f_20_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 2) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_2) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_36_function_v__29_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))))))))) (and (not expr_17_1) (= error_3 4))) (block_38_function_f__21_43_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_38_function_f__21_43_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_8_function_f__21_43_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_34_f_20_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_3 error_2) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 2) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_2) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_36_function_v__29_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))))))))))) true) (block_35_return_function_f__21_43_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_35_return_function_f__21_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_8_function_f__21_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_39_function_v__29_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_40_v_28_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_39_function_v__29_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_39_function_v__29_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_40_v_28_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_41_return_function_v__29_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_40_v_28_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_26_1) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 expr_25_0) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 x_2_1) (and (=> true true) (and (= expr_25_0 0) true)))))))) true) (block_41_return_function_v__29_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_41_return_function_v__29_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_9_function_v__29_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_42_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_43_f_41_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_42_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_42_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_43_f_41_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_44_return_function_f__42_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_45_function_f__21_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_8_function_f__21_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_45_function_f__21_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_43_f_41_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_45_function_f__21_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_10_function_f__42_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_43_f_41_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_45_function_f__21_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (block_44_return_function_f__42_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_44_return_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_10_function_f__42_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_46_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_47_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_47_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_48_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_47_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_48_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_48_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_46_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_49_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_50_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_50_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_51_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_50_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_51_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_51_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_49_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_52_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_52_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_52_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_49_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_7_B_43_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_52_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_46_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_49_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))) (> error_2 0)) (summary_constructor_7_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_2_0 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_52_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_2 0) (and (contract_initializer_46_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_49_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))))) true) (summary_constructor_7_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_2_0 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (summary_constructor_7_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_5_B_43_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_53_function_f__21_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_54_f_20_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_53_function_f__21_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_53_function_f__21_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_54_f_20_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_55_return_function_f__21_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_56_function_v__65_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_19_function_v__65_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_56_function_v__65_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_54_f_20_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_56_function_v__65_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_14_function_f__21_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_57_function_f__21_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_54_f_20_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_56_function_v__65_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))) (and (not expr_11_1) (= error_2 5))) (block_57_function_f__21_66_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_57_function_f__21_66_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_14_function_f__21_66_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_58_function_f__21_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_54_f_20_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 2) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_2) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_56_function_v__65_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))))))))) (and (not expr_17_1) (= error_3 6))) (block_58_function_f__21_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_58_function_f__21_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_14_function_f__21_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_54_f_20_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_3 error_2) (and (= expr_17_1 (= expr_15_0 expr_16_0)) (and (=> true true) (and (= expr_16_0 2) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_2_2) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 0) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_56_function_v__65_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))))))))))) true) (block_55_return_function_f__21_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_55_return_function_f__21_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_14_function_f__21_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_59_function_v__29_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_60_v_28_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_59_function_v__29_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_59_function_v__29_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_60_v_28_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_61_return_function_v__29_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_60_v_28_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_26_1) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 expr_25_0) (and (=> true (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 x_2_1) (and (=> true true) (and (= expr_25_0 0) true)))))))) true) (block_61_return_function_v__29_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_61_return_function_v__29_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_15_function_v__29_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_62_function_f__42_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_63_f_41_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_62_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_62_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_63_f_41_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_64_return_function_f__42_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_65_function_f__21_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_14_function_f__21_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_65_function_f__21_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_63_f_41_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_65_function_f__21_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_16_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_63_f_41_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_65_function_f__21_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (block_64_return_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_64_return_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_16_function_f__42_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_66_function_g__56_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_67_g_55_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_66_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_66_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_67_g_55_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_68_return_function_g__56_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_69_function_f__42_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_16_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3) (summary_69_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_67_g_55_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_69_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_2 state_2 x_2_3) (and (= x_2_2 expr_50_1) (and (=> true (and (>= expr_50_1 0) (<= expr_50_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_1 expr_49_0) (and (=> true (and (>= expr_48_0 0) (<= expr_48_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_48_0 x_2_1) (and (=> true true) (and (= expr_49_0 1) true))))))))) (> error_1 0)) (summary_17_function_g__56_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_67_g_55_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_69_function_f__42_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_2 state_2 x_2_3) (and (= x_2_2 expr_50_1) (and (=> true (and (>= expr_50_1 0) (<= expr_50_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_1 expr_49_0) (and (=> true (and (>= expr_48_0 0) (<= expr_48_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_48_0 x_2_1) (and (=> true true) (and (= expr_49_0 1) true)))))))))) true) (block_68_return_function_g__56_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_68_return_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_17_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_70_function_g__56_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_70_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_70_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_17_function_g__56_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_7_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_7_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_7_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_7_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_18_function_g__56_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_11_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_18_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_11_C_66_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_71_function_v__65_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_72_v_64_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_71_function_v__65_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_71_function_v__65_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_72_v_64_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_73_return_function_v__65_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_72_v_64_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_62_1) (and (=> true (and (>= expr_62_1 0) (<= expr_62_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_62_1 expr_61_0) (and (=> true (and (>= expr_60_0 0) (<= expr_60_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_60_0 x_2_1) (and (=> true true) (and (= expr_61_0 2) true)))))))) true) (block_73_return_function_v__65_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_73_return_function_v__65_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_19_function_v__65_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_74_C_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_75_C_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_75_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_76_C_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_75_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_76_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_76_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_74_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_77_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_78_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_78_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_79_B_43_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_78_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_79_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_79_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_77_B_43_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_80_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_81_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_81_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_82_A_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_81_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_82_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_82_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_80_A_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_83_C_66_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_83_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_83_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_80_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_13_C_66_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_83_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_77_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_80_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))) (> error_2 0)) (summary_constructor_13_C_66_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_2_0 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (implicit_constructor_entry_83_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_74_C_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 x_2_3 x_2_4) (and (= error_2 0) (and (contract_initializer_77_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_80_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))))) (> error_3 0)) (summary_constructor_13_C_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 x_2_0 x_2_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (implicit_constructor_entry_83_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_3 0) (and (contract_initializer_74_C_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 x_2_3 x_2_4) (and (= error_2 0) (and (contract_initializer_77_B_43_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_80_A_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))))))) true) (summary_constructor_13_C_66_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 x_2_0 x_2_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (summary_constructor_13_C_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_11_C_66_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |error_target_8_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_11_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_18_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 1))) error_target_8_0)))


(declare-fun |error_target_9_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_11_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_18_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 2))) error_target_9_0)))


(declare-fun |error_target_10_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_11_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_18_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 3))) error_target_10_0)))


(declare-fun |error_target_11_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_11_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_18_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 4))) error_target_11_0)))


(declare-fun |error_target_12_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_11_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_18_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 5))) error_target_12_0)))


(declare-fun |error_target_13_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_11_C_66_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_18_function_g__56_66_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 6))) error_target_13_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Bool) (expr_24_0 Int) (expr_25_0 Int) (expr_26_1 Int) (expr_39_1 |tuple()|) (expr_48_0 Int) (expr_49_0 Int) (expr_50_1 Int) (expr_53_1 |tuple()|) (expr_60_0 Int) (expr_61_0 Int) (expr_62_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> error_target_13_0 false)))
(check-sat)