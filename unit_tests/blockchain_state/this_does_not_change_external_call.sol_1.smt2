(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_D_4_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_D_4_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_D_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_D_4_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_d__3_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_4_function_d__3_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_D_4_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_d__3_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_D_4_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_5_C_52_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_6_C_52_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_7_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_1 0) (nondet_interface_6_C_52_0 error_1 this_0 abi_0 crypto_0 state_0 t_6_0 state_0 t_6_0))))


(declare-fun |summary_8_constructor_17_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_9_function_f__51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_10_function_f__51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_6_C_52_0 error_1 this_0 abi_0 crypto_0 state_0 t_6_0 state_1 t_6_1) true) (and (= error_1 0) (summary_10_function_f__51_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 t_6_1 d_20_0 state_2 t_6_2 d_20_1))) (nondet_interface_6_C_52_0 error_2 this_0 abi_0 crypto_0 state_0 t_6_0 state_2 t_6_2))))


(assert
(forall ( (a_24_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and true (= error_0 0)) (summary_3_function_d__3_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_11_D_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_12_D_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (a_24_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_12_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_13_D_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (a_24_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_12_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_13_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (a_24_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_13_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_11_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_14_D_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (a_24_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_14_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (a_24_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_14_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_11_D_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_D_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (a_24_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_14_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_11_D_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_D_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(declare-fun |block_15_function_f__51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_16_f_50_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(block_15_function_f__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1 a_24_1)))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_function_f__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1 a_24_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= t_6_1 t_6_0))) (and true (= d_20_1 d_20_0))) true)) true) (block_16_f_50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1 a_24_1))))


(declare-fun |block_17_return_function_f__51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |nondet_call_18_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (nondet_interface_6_C_52_0 error_1 this_0 abi_0 crypto_0 state_1 t_6_1 state_2 t_6_2) (nondet_call_18_0 error_1 this_0 abi_0 crypto_0 state_1 t_6_1 state_2 t_6_2))))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_f_50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1 a_24_1) (and (nondet_call_18_0 error_1 this_0 abi_0 crypto_0 state_1 t_6_1 state_2 t_6_2) (and (=> true true) (and (= expr_30_0 d_20_1) (and (= a_24_2 expr_28_1) (and (=> true (and (>= expr_28_1 0) (<= expr_28_1 1461501637330902918203684832716283019655932542975))) (and (= expr_28_1 expr_27_0) (and (=> true true) (and (= expr_27_0 this_0) (and (and (>= d_20_1 0) (<= d_20_1 1461501637330902918203684832716283019655932542975)) (and (= a_24_1 0) true))))))))))) (> error_1 0)) (summary_9_function_f__51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_2 t_6_2 d_20_1))))


(declare-fun |block_19_function_f__51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_f_50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1 a_24_1) (and (= expr_41_1 (= expr_39_1 expr_40_0)) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 1461501637330902918203684832716283019655932542975))) (and (= expr_40_0 t_6_2) (and (=> true (and (>= expr_39_1 0) (<= expr_39_1 1461501637330902918203684832716283019655932542975))) (and (= expr_39_1 expr_38_0) (and (=> true true) (and (= expr_38_0 this_0) (and (= error_1 0) (and (nondet_call_18_0 error_1 this_0 abi_0 crypto_0 state_1 t_6_1 state_2 t_6_2) (and (=> true true) (and (= expr_30_0 d_20_1) (and (= a_24_2 expr_28_1) (and (=> true (and (>= expr_28_1 0) (<= expr_28_1 1461501637330902918203684832716283019655932542975))) (and (= expr_28_1 expr_27_0) (and (=> true true) (and (= expr_27_0 this_0) (and (and (>= d_20_1 0) (<= d_20_1 1461501637330902918203684832716283019655932542975)) (and (= a_24_1 0) true))))))))))))))))))) (and (not expr_41_1) (= error_2 1))) (block_19_function_f__51_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_2 t_6_2 d_20_1 a_24_2))))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (block_19_function_f__51_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_2 t_6_2 d_20_1 a_24_2) (summary_9_function_f__51_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_2 t_6_2 d_20_1))))


(declare-fun |block_20_function_f__51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_f_50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1 a_24_1) (and (= expr_47_1 (= expr_45_0 expr_46_0)) (and (=> true (and (>= expr_46_0 0) (<= expr_46_0 1461501637330902918203684832716283019655932542975))) (and (= expr_46_0 t_6_2) (and (=> true (and (>= expr_45_0 0) (<= expr_45_0 1461501637330902918203684832716283019655932542975))) (and (= expr_45_0 a_24_2) (and (= error_2 error_1) (and (= expr_41_1 (= expr_39_1 expr_40_0)) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 1461501637330902918203684832716283019655932542975))) (and (= expr_40_0 t_6_2) (and (=> true (and (>= expr_39_1 0) (<= expr_39_1 1461501637330902918203684832716283019655932542975))) (and (= expr_39_1 expr_38_0) (and (=> true true) (and (= expr_38_0 this_0) (and (= error_1 0) (and (nondet_call_18_0 error_1 this_0 abi_0 crypto_0 state_1 t_6_1 state_2 t_6_2) (and (=> true true) (and (= expr_30_0 d_20_1) (and (= a_24_2 expr_28_1) (and (=> true (and (>= expr_28_1 0) (<= expr_28_1 1461501637330902918203684832716283019655932542975))) (and (= expr_28_1 expr_27_0) (and (=> true true) (and (= expr_27_0 this_0) (and (and (>= d_20_1 0) (<= d_20_1 1461501637330902918203684832716283019655932542975)) (and (= a_24_1 0) true))))))))))))))))))))))))) (and (not expr_47_1) (= error_3 2))) (block_20_function_f__51_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_2 t_6_2 d_20_1 a_24_2))))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (block_20_function_f__51_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_2 t_6_2 d_20_1 a_24_2) (summary_9_function_f__51_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_2 t_6_2 d_20_1))))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_f_50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1 a_24_1) (and (= error_3 error_2) (and (= expr_47_1 (= expr_45_0 expr_46_0)) (and (=> true (and (>= expr_46_0 0) (<= expr_46_0 1461501637330902918203684832716283019655932542975))) (and (= expr_46_0 t_6_2) (and (=> true (and (>= expr_45_0 0) (<= expr_45_0 1461501637330902918203684832716283019655932542975))) (and (= expr_45_0 a_24_2) (and (= error_2 error_1) (and (= expr_41_1 (= expr_39_1 expr_40_0)) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 1461501637330902918203684832716283019655932542975))) (and (= expr_40_0 t_6_2) (and (=> true (and (>= expr_39_1 0) (<= expr_39_1 1461501637330902918203684832716283019655932542975))) (and (= expr_39_1 expr_38_0) (and (=> true true) (and (= expr_38_0 this_0) (and (= error_1 0) (and (nondet_call_18_0 error_1 this_0 abi_0 crypto_0 state_1 t_6_1 state_2 t_6_2) (and (=> true true) (and (= expr_30_0 d_20_1) (and (= a_24_2 expr_28_1) (and (=> true (and (>= expr_28_1 0) (<= expr_28_1 1461501637330902918203684832716283019655932542975))) (and (= expr_28_1 expr_27_0) (and (=> true true) (and (= expr_27_0 this_0) (and (and (>= d_20_1 0) (<= d_20_1 1461501637330902918203684832716283019655932542975)) (and (= a_24_1 0) true)))))))))))))))))))))))))) true) (block_17_return_function_f__51_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_2 t_6_2 d_20_1 a_24_2))))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_17_return_function_f__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1 a_24_1) true) true) (summary_9_function_f__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1))))


(declare-fun |block_21_function_f__51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(block_21_function_f__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1 a_24_1)))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_21_function_f__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1 a_24_1) (and (summary_9_function_f__51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 t_6_1 d_20_1 state_3 t_6_2 d_20_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 4234695194)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 252)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 104)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 82)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 26)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= t_6_1 t_6_0))) (and true (= d_20_1 d_20_0))) true))))))) true) (summary_10_function_f__51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_3 t_6_2 d_20_2))))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_5_C_52_0 this_0 abi_0 crypto_0 state_0 t_6_0) true) (and (summary_10_function_f__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1) (= error_0 0))) (interface_5_C_52_0 this_0 abi_0 crypto_0 state_1 t_6_1))))


(declare-fun |block_22_constructor_17_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_23__16_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(block_22_constructor_17_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1)))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_22_constructor_17_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= t_6_1 t_6_0))) true) true)) true) (block_23__16_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1))))


(declare-fun |block_24_return_constructor_17_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_23__16_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1) (and (= t_6_2 expr_14_1) (and (=> true (and (>= expr_14_1 0) (<= expr_14_1 1461501637330902918203684832716283019655932542975))) (and (= expr_14_1 expr_13_1) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 1461501637330902918203684832716283019655932542975))) (and (= expr_9_0 t_6_1) (and (=> true (and (>= expr_13_1 0) (<= expr_13_1 1461501637330902918203684832716283019655932542975))) (and (= expr_13_1 expr_12_0) (and (=> true true) (and (= expr_12_0 this_0) true)))))))))) true) (block_24_return_constructor_17_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_2))))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_24_return_constructor_17_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1) true) true) (summary_8_constructor_17_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1))))


(declare-fun |contract_initializer_25_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_26_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= t_6_1 t_6_0))) true) (contract_initializer_entry_26_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1))))


(declare-fun |contract_initializer_after_init_27_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_26_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1) true) true) (contract_initializer_after_init_27_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1))))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_27_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1) (and (summary_8_constructor_17_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 t_6_1 state_2 t_6_2) true)) (> error_1 0)) (contract_initializer_25_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_2 t_6_2))))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_27_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1) (and (= error_1 0) (and (summary_8_constructor_17_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 t_6_1 state_2 t_6_2) true))) true) (contract_initializer_25_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_2 t_6_2))))


(declare-fun |implicit_constructor_entry_28_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= t_6_2 t_6_0))) true) (and true (= t_6_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_28_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_2 t_6_2))))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_28_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1) (and (contract_initializer_25_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 t_6_1 state_2 t_6_2) true)) (> error_1 0)) (summary_constructor_7_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_2 t_6_2))))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_28_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1) (and (= error_1 0) (and (contract_initializer_25_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 t_6_1 state_2 t_6_2) true))) true) (summary_constructor_7_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_2 t_6_2))))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_7_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 state_1 t_6_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_5_C_52_0 this_0 abi_0 crypto_0 state_1 t_6_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_5_C_52_0 this_0 abi_0 crypto_0 state_0 t_6_0) true) (and (summary_10_function_f__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 t_6_0 d_20_0 state_1 t_6_1 d_20_1) (= error_0 1))) error_target_4_0)))


(assert
(forall ( (a_24_0 Int) (a_24_1 Int) (a_24_2 Int) (a_24_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_20_0 Int) (d_20_1 Int) (d_20_2 Int) (d_20_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_12_0 Int) (expr_13_1 Int) (expr_14_1 Int) (expr_27_0 Int) (expr_28_1 Int) (expr_30_0 Int) (expr_33_1 |tuple()|) (expr_38_0 Int) (expr_39_1 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_6_0 Int) (t_6_1 Int) (t_6_2 Int) (t_6_3 Int) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_4_0 false)))
(check-sat)