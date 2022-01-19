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
(declare-fun |interface_6_L_17_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_7_L_17_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_8_L_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_1 0) (nondet_interface_7_L_17_0 error_1 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_9_function_f__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_10_C_61_0| (Int |abi_type| |crypto_type| |state_type| Int Bool ) Bool)
(declare-fun |nondet_interface_11_C_61_0| (Int Int |abi_type| |crypto_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(declare-fun |summary_constructor_12_C_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Bool Int Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (inG_21_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int))
(=> (= error_1 0) (nondet_interface_11_C_61_0 error_1 this_0 abi_0 crypto_0 state_0 x_19_0 inG_21_0 state_0 x_19_0 inG_21_0))))


(declare-fun |summary_13_function_f__16_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |summary_14_function_s__33_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(declare-fun |summary_15_function_s__33_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and (and (nondet_interface_11_C_61_0 error_1 this_0 abi_0 crypto_0 state_0 x_19_0 inG_21_0 state_1 x_19_1 inG_21_1) true) (and (= error_1 0) (summary_15_function_s__33_61_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_19_1 inG_21_1 state_2 x_19_2 inG_21_2))) (nondet_interface_11_C_61_0 error_2 this_0 abi_0 crypto_0 state_0 x_19_0 inG_21_0 state_2 x_19_2 inG_21_2))))


(declare-fun |summary_16_function_g__60_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |summary_17_function_g__60_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and (and (nondet_interface_11_C_61_0 error_2 this_0 abi_0 crypto_0 state_0 x_19_0 inG_21_0 state_1 x_19_1 inG_21_1) true) (and (= error_2 0) (summary_17_function_g__60_61_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 x_19_1 inG_21_1 _i_36_0 state_2 x_19_2 inG_21_2 _i_36_1))) (nondet_interface_11_C_61_0 error_3 this_0 abi_0 crypto_0 state_0 x_19_0 inG_21_0 state_2 x_19_2 inG_21_2))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and true (= error_0 0)) (summary_3_function_i__3_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_18_function_f__16_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_19_f_15_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(block_18_function_f__16_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1)))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and (and (block_18_function_f__16_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= _i_7_1 _i_7_0))) true)) true) (block_19_f_15_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1))))


(declare-fun |block_20_return_function_f__16_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |nondet_call_21_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (nondet_interface_1_I_4_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (nondet_call_21_0 error_1 this_0 abi_0 crypto_0 state_1 state_2))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and (and (block_19_f_15_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (and (nondet_call_21_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (and (=> true true) (and (= expr_10_0 _i_7_1) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) true))))) (> error_1 0)) (summary_5_function_f__16_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and (and (block_19_f_15_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (and (= error_1 0) (and (nondet_call_21_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (and (=> true true) (and (= expr_10_0 _i_7_1) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) true)))))) true) (block_20_return_function_f__16_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and (and (block_20_return_function_f__16_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) true) true) (summary_5_function_f__16_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1))))


(declare-fun |contract_initializer_22_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_23_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_23_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_24_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and (and (contract_initializer_entry_23_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_24_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and (and (contract_initializer_after_init_24_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_22_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_25_I_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_25_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and (and (implicit_constructor_entry_25_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_22_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_7_0 Int) (_i_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int))
(=> (and (and (implicit_constructor_entry_25_I_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_22_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_I_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(declare-fun |block_26_function_f__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_27_f_15_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(block_26_function_f__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1)))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(=> (and (and (block_26_function_f__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= _i_7_1 _i_7_0))) true)) true) (block_27_f_15_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1))))


(declare-fun |block_28_return_function_f__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |nondet_call_29_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(=> (nondet_interface_7_L_17_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (nondet_call_29_0 error_1 this_0 abi_0 crypto_0 state_1 state_2))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(=> (and (and (block_27_f_15_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (and (nondet_call_29_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (and (=> true true) (and (= expr_10_0 _i_7_1) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) true))))) (> error_1 0)) (summary_9_function_f__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(=> (and (and (block_27_f_15_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) (and (= error_1 0) (and (nondet_call_29_0 error_1 this_0 abi_0 crypto_0 state_1 state_2) (and (=> true true) (and (= expr_10_0 _i_7_1) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) true)))))) true) (block_28_return_function_f__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_2 _i_7_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(=> (and (and (block_28_return_function_f__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1) true) true) (summary_9_function_f__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _i_7_0 state_1 _i_7_1))))


(declare-fun |contract_initializer_30_L_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_31_L_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_31_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_32_L_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(=> (and (and (contract_initializer_entry_31_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_32_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(=> (and (and (contract_initializer_after_init_32_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_30_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_33_L_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_33_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(=> (and (and (implicit_constructor_entry_33_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_30_L_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_8_L_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(=> (and (and (implicit_constructor_entry_33_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_30_L_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_8_L_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int))
(=> (and (and (summary_constructor_8_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_6_L_17_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_34_function_f__16_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |block_35_f_15_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(block_34_function_f__16_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_7_0 state_1 x_19_1 inG_21_1 _i_7_1)))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_34_function_f__16_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_7_0 state_1 x_19_1 inG_21_1 _i_7_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_19_1 x_19_0)) (= inG_21_1 inG_21_0))) (and true (= _i_7_1 _i_7_0))) true)) true) (block_35_f_15_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_7_0 state_1 x_19_1 inG_21_1 _i_7_1))))


(declare-fun |block_36_return_function_f__16_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |nondet_call_37_0| (Int Int |abi_type| |crypto_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (nondet_interface_11_C_61_0 error_1 this_0 abi_0 crypto_0 state_1 x_19_1 inG_21_1 state_2 x_19_2 inG_21_2) (nondet_call_37_0 error_1 this_0 abi_0 crypto_0 state_1 x_19_1 inG_21_1 state_2 x_19_2 inG_21_2))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_35_f_15_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_7_0 state_1 x_19_1 inG_21_1 _i_7_1) (and (nondet_call_37_0 error_1 this_0 abi_0 crypto_0 state_1 x_19_1 inG_21_1 state_2 x_19_2 inG_21_2) (and (=> true true) (and (= expr_10_0 _i_7_1) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) true))))) (> error_1 0)) (summary_13_function_f__16_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_7_0 state_2 x_19_2 inG_21_2 _i_7_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_35_f_15_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_7_0 state_1 x_19_1 inG_21_1 _i_7_1) (and (= error_1 0) (and (nondet_call_37_0 error_1 this_0 abi_0 crypto_0 state_1 x_19_1 inG_21_1 state_2 x_19_2 inG_21_2) (and (=> true true) (and (= expr_10_0 _i_7_1) (and (and (>= _i_7_1 0) (<= _i_7_1 1461501637330902918203684832716283019655932542975)) true)))))) true) (block_36_return_function_f__16_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_7_0 state_2 x_19_2 inG_21_2 _i_7_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_36_return_function_f__16_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_7_0 state_1 x_19_1 inG_21_1 _i_7_1) true) true) (summary_13_function_f__16_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_7_0 state_1 x_19_1 inG_21_1 _i_7_1))))


(declare-fun |block_38_function_s__33_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(declare-fun |block_39_s_32_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(block_38_function_s__33_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 state_1 x_19_1 inG_21_1)))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_38_function_s__33_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 state_1 x_19_1 inG_21_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_19_1 x_19_0)) (= inG_21_1 inG_21_0))) true) true)) true) (block_39_s_32_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 state_1 x_19_1 inG_21_1))))


(declare-fun |block_40_return_function_s__33_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_39_s_32_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 state_1 x_19_1 inG_21_1) (and (= x_19_2 expr_30_1) (and (=> true (and (>= expr_30_1 0) (<= expr_30_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_1 expr_29_0) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_0 x_19_1) (and (=> true true) (and (= expr_29_0 2) (and (=> true expr_25_0) (and (= expr_25_0 inG_21_1) true)))))))))) true) (block_40_return_function_s__33_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 state_1 x_19_2 inG_21_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_40_return_function_s__33_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 state_1 x_19_1 inG_21_1) true) true) (summary_14_function_s__33_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 state_1 x_19_1 inG_21_1))))


(declare-fun |block_41_function_s__33_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(block_41_function_s__33_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 state_1 x_19_1 inG_21_1)))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (funds_0_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_41_function_s__33_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 state_1 x_19_1 inG_21_1) (and (summary_14_function_s__33_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_19_1 inG_21_1 state_3 x_19_2 inG_21_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 2260145378)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 134)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 183)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 20)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 226)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_19_1 x_19_0)) (= inG_21_1 inG_21_0))) true) true))))))) true) (summary_15_function_s__33_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 state_3 x_19_2 inG_21_2))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (funds_0_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (interface_10_C_61_0 this_0 abi_0 crypto_0 state_0 x_19_0 inG_21_0) true) (and (summary_15_function_s__33_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 state_1 x_19_1 inG_21_1) (= error_0 0))) (interface_10_C_61_0 this_0 abi_0 crypto_0 state_1 x_19_1 inG_21_1))))


(declare-fun |block_42_function_g__60_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |block_43_g_59_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (funds_0_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(block_42_function_g__60_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_1 x_19_1 inG_21_1 _i_36_1)))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (funds_0_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_42_function_g__60_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_1 x_19_1 inG_21_1 _i_36_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_19_1 x_19_0)) (= inG_21_1 inG_21_0))) (and true (= _i_36_1 _i_36_0))) true)) true) (block_43_g_59_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_1 x_19_1 inG_21_1 _i_36_1))))


(declare-fun |block_44_return_function_g__60_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(declare-fun |summary_45_function_f__16_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (funds_0_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (summary_13_function_f__16_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_7_0 state_2 x_19_2 inG_21_3 _i_7_2) (summary_45_function_f__16_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_7_0 state_2 x_19_2 inG_21_3 _i_7_2))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (funds_0_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_43_g_59_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_1 x_19_1 inG_21_1 _i_36_1) (and (summary_45_function_f__16_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_19_1 inG_21_2 expr_46_0 state_2 x_19_2 inG_21_3 _i_7_2) (and (=> true true) (and (= expr_46_0 _i_36_1) (and (= inG_21_2 expr_41_1) (and (= expr_41_1 expr_40_0) (and (= expr_39_0 inG_21_1) (and (= expr_40_0 true) (and (and (>= _i_36_1 0) (<= _i_36_1 1461501637330902918203684832716283019655932542975)) true))))))))) (> error_1 0)) (summary_16_function_g__60_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_2 x_19_2 inG_21_3 _i_36_1))))


(declare-fun |block_46_function_g__60_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (funds_0_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_43_g_59_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_1 x_19_1 inG_21_1 _i_36_1) (and (= expr_52_1 (= expr_50_0 expr_51_0)) (and (=> true true) (and (= expr_51_0 0) (and (=> true (and (>= expr_50_0 0) (<= expr_50_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_0 x_19_2) (and (= error_1 0) (and (summary_45_function_f__16_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_19_1 inG_21_2 expr_46_0 state_2 x_19_2 inG_21_3 _i_7_2) (and (=> true true) (and (= expr_46_0 _i_36_1) (and (= inG_21_2 expr_41_1) (and (= expr_41_1 expr_40_0) (and (= expr_39_0 inG_21_1) (and (= expr_40_0 true) (and (and (>= _i_36_1 0) (<= _i_36_1 1461501637330902918203684832716283019655932542975)) true))))))))))))))) (and (not expr_52_1) (= error_2 1))) (block_46_function_g__60_61_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_2 x_19_2 inG_21_3 _i_36_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (funds_0_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (block_46_function_g__60_61_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_2 x_19_2 inG_21_3 _i_36_1) (summary_16_function_g__60_61_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_2 x_19_2 inG_21_3 _i_36_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_43_g_59_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_1 x_19_1 inG_21_1 _i_36_1) (and (= inG_21_4 expr_57_1) (and (= expr_57_1 expr_56_0) (and (= expr_55_0 inG_21_3) (and (= expr_56_0 false) (and (= error_2 error_1) (and (= expr_52_1 (= expr_50_0 expr_51_0)) (and (=> true true) (and (= expr_51_0 0) (and (=> true (and (>= expr_50_0 0) (<= expr_50_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_0 x_19_2) (and (= error_1 0) (and (summary_45_function_f__16_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_19_1 inG_21_2 expr_46_0 state_2 x_19_2 inG_21_3 _i_7_2) (and (=> true true) (and (= expr_46_0 _i_36_1) (and (= inG_21_2 expr_41_1) (and (= expr_41_1 expr_40_0) (and (= expr_39_0 inG_21_1) (and (= expr_40_0 true) (and (and (>= _i_36_1 0) (<= _i_36_1 1461501637330902918203684832716283019655932542975)) true)))))))))))))))))))) true) (block_44_return_function_g__60_61_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_2 x_19_2 inG_21_4 _i_36_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_44_return_function_g__60_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_1 x_19_1 inG_21_1 _i_36_1) true) true) (summary_16_function_g__60_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_1 x_19_1 inG_21_1 _i_36_1))))


(declare-fun |block_47_function_g__60_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Int |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(block_47_function_g__60_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_1 x_19_1 inG_21_1 _i_36_1)))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (block_47_function_g__60_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_1 x_19_1 inG_21_1 _i_36_1) (and (summary_16_function_g__60_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_19_1 inG_21_1 _i_36_1 state_3 x_19_2 inG_21_2 _i_36_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3403328703)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 202)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 218)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 172)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 191)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_19_1 x_19_0)) (= inG_21_1 inG_21_0))) (and true (= _i_36_1 _i_36_0))) true))))))) true) (summary_17_function_g__60_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_3 x_19_2 inG_21_2 _i_36_2))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (interface_10_C_61_0 this_0 abi_0 crypto_0 state_0 x_19_0 inG_21_0) true) (and (summary_17_function_g__60_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_1 x_19_1 inG_21_1 _i_36_1) (= error_0 0))) (interface_10_C_61_0 this_0 abi_0 crypto_0 state_1 x_19_1 inG_21_1))))


(declare-fun |contract_initializer_48_C_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Bool Int Bool ) Bool)
(declare-fun |contract_initializer_entry_49_C_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Bool Int Bool ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_19_1 x_19_0)) (= inG_21_1 inG_21_0))) (contract_initializer_entry_49_C_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_19_0 inG_21_0 x_19_1 inG_21_1))))


(declare-fun |contract_initializer_after_init_50_C_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Bool Int Bool ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (contract_initializer_entry_49_C_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_19_0 inG_21_0 x_19_1 inG_21_1) true) true) (contract_initializer_after_init_50_C_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_19_0 inG_21_0 x_19_1 inG_21_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (contract_initializer_after_init_50_C_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_19_0 inG_21_0 x_19_1 inG_21_1) true) true) (contract_initializer_48_C_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_19_0 inG_21_0 x_19_1 inG_21_1))))


(declare-fun |implicit_constructor_entry_51_C_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Bool Int Bool ) Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_19_1 x_19_0)) (= inG_21_1 inG_21_0))) (and (and true (= x_19_1 0)) (= inG_21_1 false))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_51_C_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_19_0 inG_21_0 x_19_1 inG_21_1))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (implicit_constructor_entry_51_C_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_19_0 inG_21_0 x_19_1 inG_21_1) (and (contract_initializer_48_C_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_19_1 inG_21_1 x_19_2 inG_21_2) true)) (> error_1 0)) (summary_constructor_12_C_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_19_0 inG_21_0 x_19_2 inG_21_2))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (implicit_constructor_entry_51_C_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_19_0 inG_21_0 x_19_1 inG_21_1) (and (= error_1 0) (and (contract_initializer_48_C_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_19_1 inG_21_1 x_19_2 inG_21_2) true))) true) (summary_constructor_12_C_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_19_0 inG_21_0 x_19_2 inG_21_2))))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (summary_constructor_12_C_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_19_0 inG_21_0 x_19_1 inG_21_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_10_C_61_0 this_0 abi_0 crypto_0 state_1 x_19_1 inG_21_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> (and (and (interface_10_C_61_0 this_0 abi_0 crypto_0 state_0 x_19_0 inG_21_0) true) (and (summary_17_function_g__60_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_19_0 inG_21_0 _i_36_0 state_1 x_19_1 inG_21_1 _i_36_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (_i_36_0 Int) (_i_36_1 Int) (_i_36_2 Int) (_i_36_3 Int) (_i_36_4 Int) (_i_36_5 Int) (_i_7_0 Int) (_i_7_1 Int) (_i_7_2 Int) (_i_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 Int) (expr_13_1 |tuple()|) (expr_25_0 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_39_0 Bool) (expr_40_0 Bool) (expr_41_1 Bool) (expr_46_0 Int) (expr_47_1 |tuple()|) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_55_0 Bool) (expr_56_0 Bool) (expr_57_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (inG_21_0 Bool) (inG_21_1 Bool) (inG_21_2 Bool) (inG_21_3 Bool) (inG_21_4 Bool) (inG_21_5 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_19_0 Int) (x_19_1 Int) (x_19_2 Int) (x_19_3 Int) (x_19_4 Int) (x_19_5 Int))
(=> error_target_3_0 false)))
(check-sat)