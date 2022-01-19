(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_I_4_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_I_4_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_I_4_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_i__3_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_4_function_i__3_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_I_4_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_i__3_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_I_4_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_5_function_f__16_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_6_function_g__27_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_7_L_28_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_8_L_28_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_9_L_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_1 0) (nondet_interface_8_L_28_0 error_1 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_10_function_f__16_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_11_function_g__27_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_12_C_72_0| (Int |abi_type| |crypto_type| |state_type| Int Bool ) Bool)
(declare-fun |nondet_interface_13_C_72_0| (Int Int |abi_type| |crypto_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(declare-fun |summary_constructor_14_C_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Bool Int Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (inG_32_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int))
(=> (= error_1 0) (nondet_interface_13_C_72_0 error_1 this_0 abi_0 crypto_0 state_0 x_30_0 inG_32_0 state_0 x_30_0 inG_32_0))))


(declare-fun |summary_15_function_f__16_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |summary_16_function_g__27_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |summary_17_function_s__44_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(declare-fun |summary_18_function_s__44_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (nondet_interface_13_C_72_0 error_1 this_0 abi_0 crypto_0 state_0 x_30_0 inG_32_0 state_1 x_30_1 inG_32_1) true) (and (= error_1 0) (summary_18_function_s__44_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_30_1 inG_32_1 state_2 x_30_2 inG_32_2))) (nondet_interface_13_C_72_0 error_2 this_0 abi_0 crypto_0 state_0 x_30_0 inG_32_0 state_2 x_30_2 inG_32_2))))


(declare-fun |summary_19_function_g__71_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |summary_20_function_g__71_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_47_0 Int) (_i_47_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (nondet_interface_13_C_72_0 error_2 this_0 abi_0 crypto_0 state_0 x_30_0 inG_32_0 state_1 x_30_1 inG_32_1) true) (and (= error_2 0) (summary_20_function_g__71_72_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 x_30_1 inG_32_1 _i_47_0 state_2 x_30_2 inG_32_2 _i_47_1))) (nondet_interface_13_C_72_0 error_3 this_0 abi_0 crypto_0 state_0 x_30_0 inG_32_0 state_2 x_30_2 inG_32_2))))


(assert
(forall ( (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and true (= error_0 0)) (summary_3_function_i__3_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_21_function_f__16_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_22_f_15_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(block_21_function_f__16_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1)))


(assert
(forall ( (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (block_21_function_f__16_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= _i_7_1 _i_7_0))) true)) true) (block_22_f_15_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1))))


(declare-fun |block_23_return_function_f__16_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |nondet_call_24_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (nondet_interface_1_I_4_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (nondet_call_24_0 error_1 this_0 abi_0 crypto_0 state_1 state_2))))


(assert
(forall ( (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (block_22_f_15_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (and (nondet_call_24_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (and (=> true true) (and (= expr_10_0 _i_7_1) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) true))))) (> error_1 0)) (summary_5_function_f__16_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1))))


(assert
(forall ( (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (block_22_f_15_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (and (= error_1 0) (and (nondet_call_24_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (and (=> true true) (and (= expr_10_0 _i_7_1) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) true)))))) true) (block_23_return_function_f__16_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1))))


(assert
(forall ( (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (block_23_return_function_f__16_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) true) true) (summary_5_function_f__16_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1))))


(declare-fun |block_25_function_g__27_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_26_g_26_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(block_25_function_g__27_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1)))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (block_25_function_g__27_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= _i_19_1 _i_19_0))) true)) true) (block_26_g_26_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1))))


(declare-fun |block_27_return_function_g__27_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_28_function_f__16_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (summary_5_function_f__16_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_2) (summary_28_function_f__16_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (block_26_g_26_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1) (and (summary_28_function_f__16_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 expr_23_0 state_2 _i_7_2) (and (=> true true) (and (= expr_23_0 _i_19_1) (and (and (>= _i_19_1 0) (<= _i_19_1 1461501637330902918203684832716283019655932542975)) true))))) (> error_1 0)) (summary_6_function_g__27_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_2 _i_19_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (block_26_g_26_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1) (and (= error_1 0) (and (summary_28_function_f__16_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 expr_23_0 state_2 _i_7_2) (and (=> true true) (and (= expr_23_0 _i_19_1) (and (and (>= _i_19_1 0) (<= _i_19_1 1461501637330902918203684832716283019655932542975)) true)))))) true) (block_27_return_function_g__27_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_2 _i_19_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (block_27_return_function_g__27_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1) true) true) (summary_6_function_g__27_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1))))


(declare-fun |contract_initializer_29_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_30_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_30_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_31_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (contract_initializer_entry_30_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_31_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (contract_initializer_after_init_31_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_29_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_32_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_32_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (implicit_constructor_entry_32_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_29_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int))
(=> (and (and (implicit_constructor_entry_32_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_29_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(declare-fun |block_33_function_f__16_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_34_f_15_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(block_33_function_f__16_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1)))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (block_33_function_f__16_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= _i_7_1 _i_7_0))) true)) true) (block_34_f_15_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1))))


(declare-fun |block_35_return_function_f__16_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |nondet_call_36_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (nondet_interface_8_L_28_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (nondet_call_36_0 error_1 this_0 abi_0 crypto_0 state_1 state_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (block_34_f_15_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (and (nondet_call_36_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (and (=> true true) (and (= expr_10_0 _i_7_1) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) true))))) (> error_1 0)) (summary_10_function_f__16_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (block_34_f_15_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (and (= error_1 0) (and (nondet_call_36_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (and (=> true true) (and (= expr_10_0 _i_7_1) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) true)))))) true) (block_35_return_function_f__16_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (block_35_return_function_f__16_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) true) true) (summary_10_function_f__16_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1))))


(declare-fun |block_37_function_g__27_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_38_g_26_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(block_37_function_g__27_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1)))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (block_37_function_g__27_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= _i_19_1 _i_19_0))) true)) true) (block_38_g_26_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1))))


(declare-fun |block_39_return_function_g__27_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_40_function_f__16_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (summary_10_function_f__16_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_2) (summary_40_function_f__16_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (block_38_g_26_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1) (and (summary_40_function_f__16_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 expr_23_0 state_1 _i_7_2) (and (=> true true) (and (= expr_23_0 _i_19_1) (and (and (>= _i_19_1 0) (<= _i_19_1 1461501637330902918203684832716283019655932542975)) true))))) (> error_1 0)) (summary_11_function_g__27_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (block_38_g_26_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1) (and (= error_1 0) (and (summary_40_function_f__16_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 expr_23_0 state_1 _i_7_2) (and (=> true true) (and (= expr_23_0 _i_19_1) (and (and (>= _i_19_1 0) (<= _i_19_1 1461501637330902918203684832716283019655932542975)) true)))))) true) (block_39_return_function_g__27_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (block_39_return_function_g__27_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1) true) true) (summary_11_function_g__27_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_19_0 state_1 _i_19_1))))


(declare-fun |contract_initializer_41_L_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_42_L_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_42_L_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_43_L_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (contract_initializer_entry_42_L_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_43_L_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (contract_initializer_after_init_43_L_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_41_L_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_44_L_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_44_L_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (implicit_constructor_entry_44_L_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_41_L_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_9_L_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (implicit_constructor_entry_44_L_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_41_L_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_9_L_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int))
(=> (and (and (summary_constructor_9_L_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_7_L_28_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_45_function_f__16_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |block_46_f_15_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(block_45_function_f__16_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_7_0 state_1 x_30_1 inG_32_1 _i_7_1)))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_45_function_f__16_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_7_0 state_1 x_30_1 inG_32_1 _i_7_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_30_1 x_30_0)) (= inG_32_1 inG_32_0))) (and true (= _i_7_1 _i_7_0))) true)) true) (block_46_f_15_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_7_0 state_1 x_30_1 inG_32_1 _i_7_1))))


(declare-fun |block_47_return_function_f__16_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |nondet_call_48_0| (Int Int |abi_type| |crypto_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (nondet_interface_13_C_72_0 error_1 this_0 abi_0 crypto_0 state_1 x_30_1 inG_32_1 state_2 x_30_2 inG_32_2) (nondet_call_48_0 error_1 this_0 abi_0 crypto_0 state_1 x_30_1 inG_32_1 state_2 x_30_2 inG_32_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_46_f_15_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_7_0 state_1 x_30_1 inG_32_1 _i_7_1) (and (nondet_call_48_0 error_1 this_0 abi_0 crypto_0 state_1 x_30_1 inG_32_1 state_2 x_30_2 inG_32_2) (and (=> true true) (and (= expr_10_0 _i_7_1) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) true))))) (> error_1 0)) (summary_15_function_f__16_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_7_0 state_2 x_30_2 inG_32_2 _i_7_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_46_f_15_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_7_0 state_1 x_30_1 inG_32_1 _i_7_1) (and (= error_1 0) (and (nondet_call_48_0 error_1 this_0 abi_0 crypto_0 state_1 x_30_1 inG_32_1 state_2 x_30_2 inG_32_2) (and (=> true true) (and (= expr_10_0 _i_7_1) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) true)))))) true) (block_47_return_function_f__16_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_7_0 state_2 x_30_2 inG_32_2 _i_7_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_47_return_function_f__16_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_7_0 state_1 x_30_1 inG_32_1 _i_7_1) true) true) (summary_15_function_f__16_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_7_0 state_1 x_30_1 inG_32_1 _i_7_1))))


(declare-fun |block_49_function_g__27_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |block_50_g_26_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(block_49_function_g__27_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_19_0 state_1 x_30_1 inG_32_1 _i_19_1)))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_49_function_g__27_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_19_0 state_1 x_30_1 inG_32_1 _i_19_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_30_1 x_30_0)) (= inG_32_1 inG_32_0))) (and true (= _i_19_1 _i_19_0))) true)) true) (block_50_g_26_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_19_0 state_1 x_30_1 inG_32_1 _i_19_1))))


(declare-fun |block_51_return_function_g__27_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |summary_52_function_f__16_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (summary_15_function_f__16_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_7_0 state_2 x_30_2 inG_32_2 _i_7_2) (summary_52_function_f__16_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_7_0 state_2 x_30_2 inG_32_2 _i_7_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_50_g_26_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_19_0 state_1 x_30_1 inG_32_1 _i_19_1) (and (summary_52_function_f__16_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_30_1 inG_32_1 expr_23_0 state_2 x_30_2 inG_32_2 _i_7_2) (and (=> true true) (and (= expr_23_0 _i_19_1) (and (and (>= _i_19_1 0) (<= _i_19_1 1461501637330902918203684832716283019655932542975)) true))))) (> error_1 0)) (summary_16_function_g__27_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_19_0 state_2 x_30_2 inG_32_2 _i_19_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_50_g_26_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_19_0 state_1 x_30_1 inG_32_1 _i_19_1) (and (= error_1 0) (and (summary_52_function_f__16_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_30_1 inG_32_1 expr_23_0 state_2 x_30_2 inG_32_2 _i_7_2) (and (=> true true) (and (= expr_23_0 _i_19_1) (and (and (>= _i_19_1 0) (<= _i_19_1 1461501637330902918203684832716283019655932542975)) true)))))) true) (block_51_return_function_g__27_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_19_0 state_2 x_30_2 inG_32_2 _i_19_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_51_return_function_g__27_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_19_0 state_1 x_30_1 inG_32_1 _i_19_1) true) true) (summary_16_function_g__27_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_19_0 state_1 x_30_1 inG_32_1 _i_19_1))))


(declare-fun |block_53_function_s__44_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(declare-fun |block_54_s_43_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(block_53_function_s__44_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 state_1 x_30_1 inG_32_1)))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_53_function_s__44_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 state_1 x_30_1 inG_32_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_30_1 x_30_0)) (= inG_32_1 inG_32_0))) true) true)) true) (block_54_s_43_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 state_1 x_30_1 inG_32_1))))


(declare-fun |block_55_return_function_s__44_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_54_s_43_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 state_1 x_30_1 inG_32_1) (and (= x_30_2 expr_41_1) (and (=> true (and (>= expr_41_1 0) (<= expr_41_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_41_1 expr_40_0) (and (=> true (and (>= expr_39_0 0) (<= expr_39_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_39_0 x_30_1) (and (=> true true) (and (= expr_40_0 2) (and (=> true expr_36_0) (and (= expr_36_0 inG_32_1) true)))))))))) true) (block_55_return_function_s__44_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 state_1 x_30_2 inG_32_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_55_return_function_s__44_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 state_1 x_30_1 inG_32_1) true) true) (summary_17_function_s__44_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 state_1 x_30_1 inG_32_1))))


(declare-fun |block_56_function_s__44_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(block_56_function_s__44_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 state_1 x_30_1 inG_32_1)))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (funds_0_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_56_function_s__44_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 state_1 x_30_1 inG_32_1) (and (summary_17_function_s__44_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_30_1 inG_32_1 state_3 x_30_2 inG_32_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 2260145378)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 134)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 183)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 20)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 226)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_30_1 x_30_0)) (= inG_32_1 inG_32_0))) true) true))))))) true) (summary_18_function_s__44_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 state_3 x_30_2 inG_32_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (funds_0_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (interface_12_C_72_0 this_0 abi_0 crypto_0 state_0 x_30_0 inG_32_0) true) (and (summary_18_function_s__44_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 state_1 x_30_1 inG_32_1) (= error_0 0))) (interface_12_C_72_0 this_0 abi_0 crypto_0 state_1 x_30_1 inG_32_1))))


(declare-fun |block_57_function_g__71_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |block_58_g_70_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (funds_0_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(block_57_function_g__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_1 x_30_1 inG_32_1 _i_47_1)))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (funds_0_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_57_function_g__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_1 x_30_1 inG_32_1 _i_47_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_30_1 x_30_0)) (= inG_32_1 inG_32_0))) (and true (= _i_47_1 _i_47_0))) true)) true) (block_58_g_70_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_1 x_30_1 inG_32_1 _i_47_1))))


(declare-fun |block_59_return_function_g__71_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |summary_60_function_g__27_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (funds_0_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (summary_16_function_g__27_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_19_0 state_2 x_30_2 inG_32_3 _i_19_2) (summary_60_function_g__27_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_19_0 state_2 x_30_2 inG_32_3 _i_19_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (funds_0_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_58_g_70_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_1 x_30_1 inG_32_1 _i_47_1) (and (summary_60_function_g__27_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_30_1 inG_32_2 expr_57_0 state_2 x_30_2 inG_32_3 _i_19_2) (and (=> true true) (and (= expr_57_0 _i_47_1) (and (= inG_32_2 expr_52_1) (and (= expr_52_1 expr_51_0) (and (= expr_50_0 inG_32_1) (and (= expr_51_0 true) (and (and (>= _i_47_1 0) (<= _i_47_1 1461501637330902918203684832716283019655932542975)) true))))))))) (> error_1 0)) (summary_19_function_g__71_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_2 x_30_2 inG_32_3 _i_47_1))))


(declare-fun |block_61_function_g__71_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (funds_0_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_58_g_70_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_1 x_30_1 inG_32_1 _i_47_1) (and (= expr_63_1 (= expr_61_0 expr_62_0)) (and (=> true true) (and (= expr_62_0 0) (and (=> true (and (>= expr_61_0 0) (<= expr_61_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_61_0 x_30_2) (and (= error_1 0) (and (summary_60_function_g__27_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_30_1 inG_32_2 expr_57_0 state_2 x_30_2 inG_32_3 _i_19_2) (and (=> true true) (and (= expr_57_0 _i_47_1) (and (= inG_32_2 expr_52_1) (and (= expr_52_1 expr_51_0) (and (= expr_50_0 inG_32_1) (and (= expr_51_0 true) (and (and (>= _i_47_1 0) (<= _i_47_1 1461501637330902918203684832716283019655932542975)) true))))))))))))))) (and (not expr_63_1) (= error_2 1))) (block_61_function_g__71_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_2 x_30_2 inG_32_3 _i_47_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (funds_0_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (block_61_function_g__71_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_2 x_30_2 inG_32_3 _i_47_1) (summary_19_function_g__71_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_2 x_30_2 inG_32_3 _i_47_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_58_g_70_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_1 x_30_1 inG_32_1 _i_47_1) (and (= inG_32_4 expr_68_1) (and (= expr_68_1 expr_67_0) (and (= expr_66_0 inG_32_3) (and (= expr_67_0 false) (and (= error_2 error_1) (and (= expr_63_1 (= expr_61_0 expr_62_0)) (and (=> true true) (and (= expr_62_0 0) (and (=> true (and (>= expr_61_0 0) (<= expr_61_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_61_0 x_30_2) (and (= error_1 0) (and (summary_60_function_g__27_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_30_1 inG_32_2 expr_57_0 state_2 x_30_2 inG_32_3 _i_19_2) (and (=> true true) (and (= expr_57_0 _i_47_1) (and (= inG_32_2 expr_52_1) (and (= expr_52_1 expr_51_0) (and (= expr_50_0 inG_32_1) (and (= expr_51_0 true) (and (and (>= _i_47_1 0) (<= _i_47_1 1461501637330902918203684832716283019655932542975)) true)))))))))))))))))))) true) (block_59_return_function_g__71_72_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_2 x_30_2 inG_32_4 _i_47_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_59_return_function_g__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_1 x_30_1 inG_32_1 _i_47_1) true) true) (summary_19_function_g__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_1 x_30_1 inG_32_1 _i_47_1))))


(declare-fun |block_62_function_g__71_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(block_62_function_g__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_1 x_30_1 inG_32_1 _i_47_1)))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (block_62_function_g__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_1 x_30_1 inG_32_1 _i_47_1) (and (summary_19_function_g__71_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_30_1 inG_32_1 _i_47_1 state_3 x_30_2 inG_32_2 _i_47_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3403328703)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 202)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 218)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 172)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 191)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_30_1 x_30_0)) (= inG_32_1 inG_32_0))) (and true (= _i_47_1 _i_47_0))) true))))))) true) (summary_20_function_g__71_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_3 x_30_2 inG_32_2 _i_47_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (interface_12_C_72_0 this_0 abi_0 crypto_0 state_0 x_30_0 inG_32_0) true) (and (summary_20_function_g__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_1 x_30_1 inG_32_1 _i_47_1) (= error_0 0))) (interface_12_C_72_0 this_0 abi_0 crypto_0 state_1 x_30_1 inG_32_1))))


(declare-fun |contract_initializer_63_C_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Bool Int Bool ) Bool)
(declare-fun |contract_initializer_entry_64_C_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Bool Int Bool ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_30_1 x_30_0)) (= inG_32_1 inG_32_0))) (contract_initializer_entry_64_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_30_0 inG_32_0 x_30_1 inG_32_1))))


(declare-fun |contract_initializer_after_init_65_C_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Bool Int Bool ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (contract_initializer_entry_64_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_30_0 inG_32_0 x_30_1 inG_32_1) true) true) (contract_initializer_after_init_65_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_30_0 inG_32_0 x_30_1 inG_32_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (contract_initializer_after_init_65_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_30_0 inG_32_0 x_30_1 inG_32_1) true) true) (contract_initializer_63_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_30_0 inG_32_0 x_30_1 inG_32_1))))


(declare-fun |implicit_constructor_entry_66_C_72_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Bool Int Bool ) Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_30_1 x_30_0)) (= inG_32_1 inG_32_0))) (and (and true (= x_30_1 0)) (= inG_32_1 false))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_66_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_30_0 inG_32_0 x_30_1 inG_32_1))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (implicit_constructor_entry_66_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_30_0 inG_32_0 x_30_1 inG_32_1) (and (contract_initializer_63_C_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_30_1 inG_32_1 x_30_2 inG_32_2) true)) (> error_1 0)) (summary_constructor_14_C_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_30_0 inG_32_0 x_30_2 inG_32_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (implicit_constructor_entry_66_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_30_0 inG_32_0 x_30_1 inG_32_1) (and (= error_1 0) (and (contract_initializer_63_C_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_30_1 inG_32_1 x_30_2 inG_32_2) true))) true) (summary_constructor_14_C_72_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_30_0 inG_32_0 x_30_2 inG_32_2))))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (summary_constructor_14_C_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_30_0 inG_32_0 x_30_1 inG_32_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_12_C_72_0 this_0 abi_0 crypto_0 state_1 x_30_1 inG_32_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> (and (and (interface_12_C_72_0 this_0 abi_0 crypto_0 state_0 x_30_0 inG_32_0) true) (and (summary_20_function_g__71_72_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_30_0 inG_32_0 _i_47_0 state_1 x_30_1 inG_32_1 _i_47_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (_i_19_0 Int) (_i_19_1 Int) (_i_19_2 Int) (_i_19_3 Int) (_i_47_0 Int) (_i_47_1 Int) (_i_47_2 Int) (_i_47_3 Int) (_i_47_4 Int) (_i_47_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (_i_7_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_23_0 Int) (expr_24_1 |tuple()|) (expr_36_0 Bool) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Int) (expr_50_0 Bool) (expr_51_0 Bool) (expr_52_1 Bool) (expr_57_0 Int) (expr_58_1 |tuple()|) (expr_61_0 Int) (expr_62_0 Int) (expr_63_1 Bool) (expr_66_0 Bool) (expr_67_0 Bool) (expr_68_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_32_0 Bool) (inG_32_1 Bool) (inG_32_2 Bool) (inG_32_3 Bool) (inG_32_4 Bool) (inG_32_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int))
(=> error_target_3_0 false)))
(check-sat)