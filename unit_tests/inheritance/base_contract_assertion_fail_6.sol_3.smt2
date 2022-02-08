(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_A_37_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_A_37_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_A_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_1_A_37_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_3_function_f__15_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_4_function_v__23_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_5_function_g__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_6_function_g__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_1_A_37_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_0 0) (summary_6_function_g__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_1_A_37_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |interface_7_B_50_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_8_B_50_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_9_B_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (= error_1 0) (nondet_interface_8_B_50_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_10_function_f__15_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_11_function_v__23_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_12_function_g__36_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_13_function_g__36_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_8_B_50_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_1 0) (summary_13_function_g__36_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_8_B_50_0 error_2 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |summary_14_function_f__49_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_15_C_74_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_16_C_74_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_17_C_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (= error_2 0) (nondet_interface_16_C_74_0 error_2 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_18_function_f__15_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_19_function_v__23_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_20_function_g__36_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_21_function_f__49_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_22_function_g__64_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_23_function_g__64_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_16_C_74_0 error_2 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_2 0) (summary_23_function_g__64_74_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_16_C_74_0 error_3 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |summary_24_function_v__73_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_25_function_f__15_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_26_f_14_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_25_function_f__15_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_25_function_f__15_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_26_f_14_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_27_return_function_f__15_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_28_function_v__23_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (summary_4_function_v__23_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_28_function_v__23_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_26_f_14_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_28_function_v__23_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_3_function_f__15_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_29_function_f__15_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_26_f_14_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 2) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_28_function_v__23_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))) (and (not expr_11_1) (= error_2 1))) (block_29_function_f__15_37_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (block_29_function_f__15_37_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_3_function_f__15_37_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_26_f_14_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 2) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_28_function_v__23_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))))) true) (block_27_return_function_f__15_37_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_27_return_function_f__15_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_3_function_f__15_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_30_function_v__23_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_31_v_22_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_30_function_v__23_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_30_function_v__23_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_31_v_22_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_32_return_function_v__23_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_31_v_22_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_20_1) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_1 expr_19_0) (and (=> true (and (>= expr_18_0 0) (<= expr_18_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_0 x_2_1) (and (=> true true) (and (= expr_19_0 0) true)))))))) true) (block_32_return_function_v__23_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_32_return_function_v__23_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_4_function_v__23_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_33_function_g__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_34_g_35_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_33_function_g__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_33_function_g__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_34_g_35_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_35_return_function_g__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_36_function_v__23_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (summary_4_function_v__23_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_36_function_v__23_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_34_g_35_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_36_function_v__23_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_5_function_g__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_37_function_g__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_34_g_35_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_32_1 (= expr_30_0 expr_31_0)) (and (=> true true) (and (= expr_31_0 2) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 x_2_2) (and (= error_1 0) (and (summary_36_function_v__23_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))) (and (not expr_32_1) (= error_2 2))) (block_37_function_g__36_37_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (block_37_function_g__36_37_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_5_function_g__36_37_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_34_g_35_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_2 error_1) (and (= expr_32_1 (= expr_30_0 expr_31_0)) (and (=> true true) (and (= expr_31_0 2) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 x_2_2) (and (= error_1 0) (and (summary_36_function_v__23_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))))) true) (block_35_return_function_g__36_37_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_35_return_function_g__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_5_function_g__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_38_function_g__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_38_function_g__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_38_function_g__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_5_function_g__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_6_function_g__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (interface_0_A_37_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_6_function_g__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_0_A_37_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |contract_initializer_39_A_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_40_A_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_40_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_41_A_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_entry_40_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_41_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_after_init_41_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_39_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_42_A_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_42_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_42_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_39_A_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_2_A_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_42_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_1 0) (and (contract_initializer_39_A_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))) true) (summary_constructor_2_A_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (summary_constructor_2_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_37_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_43_function_f__15_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_44_f_14_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_43_function_f__15_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_43_function_f__15_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_44_f_14_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_45_return_function_f__15_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_46_function_v__23_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_11_function_v__23_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_46_function_v__23_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_44_f_14_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_46_function_v__23_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_10_function_f__15_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_47_function_f__15_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_44_f_14_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 2) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_46_function_v__23_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))) (and (not expr_11_1) (= error_2 4))) (block_47_function_f__15_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_47_function_f__15_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_10_function_f__15_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_44_f_14_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 2) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_46_function_v__23_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))))) true) (block_45_return_function_f__15_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_45_return_function_f__15_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_10_function_f__15_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_48_function_v__23_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_49_v_22_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_48_function_v__23_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_48_function_v__23_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_49_v_22_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_50_return_function_v__23_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_49_v_22_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_20_1) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_1 expr_19_0) (and (=> true (and (>= expr_18_0 0) (<= expr_18_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_0 x_2_1) (and (=> true true) (and (= expr_19_0 0) true)))))))) true) (block_50_return_function_v__23_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_50_return_function_v__23_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_11_function_v__23_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_51_function_g__36_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_52_g_35_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_51_function_g__36_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_51_function_g__36_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_52_g_35_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_53_return_function_g__36_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_54_function_v__23_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_11_function_v__23_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_54_function_v__23_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_52_g_35_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_54_function_v__23_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_12_function_g__36_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_55_function_g__36_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_52_g_35_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_32_1 (= expr_30_0 expr_31_0)) (and (=> true true) (and (= expr_31_0 2) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 x_2_2) (and (= error_1 0) (and (summary_54_function_v__23_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))) (and (not expr_32_1) (= error_2 5))) (block_55_function_g__36_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_55_function_g__36_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_12_function_g__36_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_52_g_35_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_2 error_1) (and (= expr_32_1 (= expr_30_0 expr_31_0)) (and (=> true true) (and (= expr_31_0 2) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 x_2_2) (and (= error_1 0) (and (summary_54_function_v__23_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))))) true) (block_53_return_function_g__36_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_53_return_function_g__36_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_12_function_g__36_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_56_function_g__36_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_56_function_g__36_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_56_function_g__36_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_12_function_g__36_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_6_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_6_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_6_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_6_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_13_function_g__36_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_7_B_50_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_13_function_g__36_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_7_B_50_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_57_function_f__49_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_58_f_48_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_57_function_f__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_57_function_f__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_58_f_48_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_59_return_function_f__49_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_60_function_f__15_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_10_function_f__15_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_60_function_f__15_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_58_f_48_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_60_function_f__15_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_14_function_f__49_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_58_f_48_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_60_function_f__15_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (block_59_return_function_f__49_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_59_return_function_f__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_14_function_f__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_61_B_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_62_B_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_62_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_63_B_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_62_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_63_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_63_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_61_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_64_A_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_65_A_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_65_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_66_A_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_65_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_66_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_66_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_64_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_67_B_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_67_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_67_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_64_A_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_9_B_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_67_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_61_B_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_64_A_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))) (> error_2 0)) (summary_constructor_9_B_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_2_0 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_67_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_2 0) (and (contract_initializer_61_B_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_64_A_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))))) true) (summary_constructor_9_B_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_2_0 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (summary_constructor_9_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_7_B_50_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_68_function_f__15_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_69_f_14_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_68_function_f__15_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_68_function_f__15_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_69_f_14_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_70_return_function_f__15_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_71_function_v__73_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_24_function_v__73_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_71_function_v__73_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_69_f_14_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_71_function_v__73_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_18_function_f__15_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_72_function_f__15_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_69_f_14_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 2) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_71_function_v__73_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))) (and (not expr_11_1) (= error_2 7))) (block_72_function_f__15_74_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_72_function_f__15_74_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_18_function_f__15_74_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_69_f_14_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_2 error_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 2) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_2_2) (and (= error_1 0) (and (summary_71_function_v__73_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))))) true) (block_70_return_function_f__15_74_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_70_return_function_f__15_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_18_function_f__15_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_73_function_v__23_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_74_v_22_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_73_function_v__23_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_73_function_v__23_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_74_v_22_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_75_return_function_v__23_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_74_v_22_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_20_1) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_1 expr_19_0) (and (=> true (and (>= expr_18_0 0) (<= expr_18_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_0 x_2_1) (and (=> true true) (and (= expr_19_0 0) true)))))))) true) (block_75_return_function_v__23_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_75_return_function_v__23_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_19_function_v__23_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_76_function_g__36_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_77_g_35_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_76_function_g__36_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_76_function_g__36_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_77_g_35_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_78_return_function_g__36_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_79_function_v__73_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_24_function_v__73_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_79_function_v__73_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_77_g_35_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_79_function_v__73_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_20_function_g__36_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_80_function_g__36_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_77_g_35_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_32_1 (= expr_30_0 expr_31_0)) (and (=> true true) (and (= expr_31_0 2) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 x_2_2) (and (= error_1 0) (and (summary_79_function_v__73_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)))))))) (and (not expr_32_1) (= error_2 8))) (block_80_function_g__36_74_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (block_80_function_g__36_74_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_20_function_g__36_74_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_77_g_35_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_2 error_1) (and (= expr_32_1 (= expr_30_0 expr_31_0)) (and (=> true true) (and (= expr_31_0 2) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 x_2_2) (and (= error_1 0) (and (summary_79_function_v__73_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))))))))) true) (block_78_return_function_g__36_74_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_78_return_function_g__36_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_20_function_g__36_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_81_function_f__49_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_82_f_48_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_81_function_f__49_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_81_function_f__49_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_82_f_48_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_83_return_function_f__49_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_84_function_f__15_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_18_function_f__15_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2) (summary_84_function_f__15_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_82_f_48_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_84_function_f__15_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (summary_21_function_f__49_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_82_f_48_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_84_function_f__15_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (block_83_return_function_f__49_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_83_return_function_f__49_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_21_function_f__49_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_85_function_g__64_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_86_g_63_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_85_function_g__64_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_85_function_g__64_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_86_g_63_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_87_return_function_g__64_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_88_function_f__49_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (summary_21_function_f__49_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3) (summary_88_function_f__49_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_86_g_63_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_88_function_f__49_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_2 state_2 x_2_3) (and (= x_2_2 expr_58_1) (and (=> true (and (>= expr_58_1 0) (<= expr_58_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_58_1 expr_57_0) (and (=> true (and (>= expr_56_0 0) (<= expr_56_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_56_0 x_2_1) (and (=> true true) (and (= expr_57_0 1) true))))))))) (> error_1 0)) (summary_22_function_g__64_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_86_g_63_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_88_function_f__49_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_2 state_2 x_2_3) (and (= x_2_2 expr_58_1) (and (=> true (and (>= expr_58_1 0) (<= expr_58_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_58_1 expr_57_0) (and (=> true (and (>= expr_56_0 0) (<= expr_56_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_56_0 x_2_1) (and (=> true true) (and (= expr_57_0 1) true)))))))))) true) (block_87_return_function_g__64_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_87_return_function_g__64_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_22_function_g__64_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_89_function_g__64_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_89_function_g__64_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_89_function_g__64_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_22_function_g__64_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_9_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_9_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_9_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_9_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_23_function_g__64_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (interface_15_C_74_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_23_function_g__64_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_15_C_74_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_90_function_v__73_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_91_v_72_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(block_90_function_v__73_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_6_1 |tuple()|) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_90_function_v__73_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_91_v_72_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_92_return_function_v__73_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_91_v_72_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= x_2_2 expr_70_1) (and (=> true (and (>= expr_70_1 0) (<= expr_70_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_70_1 expr_69_0) (and (=> true (and (>= expr_68_0 0) (<= expr_68_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_68_0 x_2_1) (and (=> true true) (and (= expr_69_0 2) true)))))))) true) (block_92_return_function_v__73_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (block_92_return_function_v__73_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_24_function_v__73_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_93_C_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_94_C_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_94_C_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_95_C_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_94_C_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_95_C_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_95_C_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_93_C_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_96_B_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_97_B_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_97_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_98_B_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_97_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_98_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_98_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_96_B_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_99_A_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_100_A_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_100_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_101_A_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_entry_100_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_101_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (contract_initializer_after_init_101_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_99_A_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_102_C_74_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_102_C_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_102_C_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_99_A_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_17_C_74_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int))
(=> (and (and (implicit_constructor_entry_102_C_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_96_B_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_99_A_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))) (> error_2 0)) (summary_constructor_17_C_74_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_2_0 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (implicit_constructor_entry_102_C_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_93_C_74_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 x_2_3 x_2_4) (and (= error_2 0) (and (contract_initializer_96_B_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_99_A_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))))) (> error_3 0)) (summary_constructor_17_C_74_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 x_2_0 x_2_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (implicit_constructor_entry_102_C_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_3 0) (and (contract_initializer_93_C_74_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 x_2_3 x_2_4) (and (= error_2 0) (and (contract_initializer_96_B_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 x_2_2 x_2_3) (and (= error_1 0) (and (contract_initializer_99_A_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))))))) true) (summary_constructor_17_C_74_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 x_2_0 x_2_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (summary_constructor_17_C_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_15_C_74_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |error_target_10_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_15_C_74_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_23_function_g__64_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 1))) error_target_10_0)))


(declare-fun |error_target_11_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_0_A_37_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_6_function_g__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 2))) error_target_11_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_7_B_50_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_13_function_g__36_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 2))) error_target_11_0)))


(declare-fun |error_target_12_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> (and (and (interface_15_C_74_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_23_function_g__64_74_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 4))) error_target_12_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Int) (expr_27_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_46_1 |tuple()|) (expr_56_0 Int) (expr_57_0 Int) (expr_58_1 Int) (expr_61_1 |tuple()|) (expr_68_0 Int) (expr_69_0 Int) (expr_6_1 |tuple()|) (expr_70_1 Int) (expr_9_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int))
(=> error_target_12_0 false)))
(check-sat)