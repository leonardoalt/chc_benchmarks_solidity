(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_50_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_50_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_50_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__31_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_4_function_f__31_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_8_0 Int) (a_8_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_50_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_f__31_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_8_0 state_2 a_8_1))) (nondet_interface_1_C_50_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_5_function_g__49_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_6_function_g__49_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_34_1 Int) (a_8_0 Int) (a_8_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_50_0 error_1 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_1 0) (summary_6_function_g__49_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 state_2 _34_1))) (nondet_interface_1_C_50_0 error_2 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_7_function_f__31_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_8_f_30_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_34_1 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_7_function_f__31_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1)))


(assert
(forall ( (_34_1 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_function_f__31_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= a_8_1 a_8_0))) true)) true) (block_8_f_30_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1))))


(declare-fun |block_9_return_f_6_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_10_if_header_f_4_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_11_if_true_f_3_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_12_f_30_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_34_1 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_f_30_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) (and (and (>= a_8_1 0) (<= a_8_1 1461501637330902918203684832716283019655932542975)) true)) true) (block_10_if_header_f_4_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1))))


(assert
(forall ( (_34_1 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_10_if_header_f_4_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) (and (= expr_2_0 true) true)) expr_2_0) (block_11_if_true_f_3_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1))))


(assert
(forall ( (_34_1 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_10_if_header_f_4_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) (and (= expr_2_0 true) true)) (not expr_2_0)) (block_12_f_30_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1))))


(declare-fun |block_13_return_function_f__31_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_14_if_header_f_29_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_15_if_true_f_28_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_16_f_30_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_34_1 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_if_true_f_3_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) true) true) (block_14_if_header_f_29_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1))))


(assert
(forall ( (_34_1 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_if_header_f_29_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) (and (= expr_13_0 true) true)) expr_13_0) (block_15_if_true_f_28_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1))))


(assert
(forall ( (_34_1 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_if_header_f_29_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) (and (= expr_13_0 true) true)) (not expr_13_0)) (block_16_f_30_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1))))


(declare-fun |summary_17_function_g__49_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_34_1 Int) (_34_2 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_5_function_g__49_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_2) (summary_17_function_g__49_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_2))))


(assert
(forall ( (_34_1 Int) (_34_2 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_if_true_f_28_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) (and (summary_17_function_g__49_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _34_2) (and true true))) (> error_1 0)) (summary_3_function_f__31_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1))))


(declare-fun |block_18_function_f__31_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_34_1 Int) (_34_2 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_if_true_f_28_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) (and (= expr_25_1 (= expr_20_0 expr_24_1)) (and (=> true (and (>= expr_24_1 0) (<= expr_24_1 1461501637330902918203684832716283019655932542975))) (and (= expr_24_1 expr_23_0) (and (=> true true) (and (= expr_23_0 0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 1461501637330902918203684832716283019655932542975))) (and (= expr_20_0 a_8_2) (and (= a_8_2 expr_17_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 1461501637330902918203684832716283019655932542975))) (and (= expr_17_1 expr_16_0) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 1461501637330902918203684832716283019655932542975))) (and (= expr_14_0 a_8_1) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 1461501637330902918203684832716283019655932542975))) (and (= expr_16_0 _34_2) (and (= error_1 0) (and (summary_17_function_g__49_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _34_2) (and true true)))))))))))))))))) (and (not expr_25_1) (= error_2 1))) (block_18_function_f__31_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_2))))


(assert
(forall ( (_34_1 Int) (_34_2 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (block_18_function_f__31_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_2) (summary_3_function_f__31_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_2))))


(assert
(forall ( (_34_1 Int) (_34_2 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_if_true_f_28_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) (and (= error_2 error_1) (and (= expr_25_1 (= expr_20_0 expr_24_1)) (and (=> true (and (>= expr_24_1 0) (<= expr_24_1 1461501637330902918203684832716283019655932542975))) (and (= expr_24_1 expr_23_0) (and (=> true true) (and (= expr_23_0 0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 1461501637330902918203684832716283019655932542975))) (and (= expr_20_0 a_8_2) (and (= a_8_2 expr_17_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 1461501637330902918203684832716283019655932542975))) (and (= expr_17_1 expr_16_0) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 1461501637330902918203684832716283019655932542975))) (and (= expr_14_0 a_8_1) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 1461501637330902918203684832716283019655932542975))) (and (= expr_16_0 _34_2) (and (= error_1 0) (and (summary_17_function_g__49_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _34_2) (and true true))))))))))))))))))) true) (block_16_f_30_50_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_2))))


(assert
(forall ( (_34_1 Int) (_34_2 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_f_30_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) true) true) (block_13_return_function_f__31_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1))))


(assert
(forall ( (_34_1 Int) (_34_2 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_return_function_f__31_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) true) true) (block_12_f_30_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1))))


(assert
(forall ( (_34_1 Int) (_34_2 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_f_30_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) true) true) (block_9_return_f_6_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1))))


(assert
(forall ( (_34_1 Int) (_34_2 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_9_return_f_6_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) true) true) (summary_3_function_f__31_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1))))


(declare-fun |block_19_function_f__31_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_34_1 Int) (_34_2 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(block_19_function_f__31_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1)))


(assert
(forall ( (_34_1 Int) (_34_2 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_19_function_f__31_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) (and (summary_3_function_f__31_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 a_8_1 state_3 a_8_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 4234695194)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 252)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 104)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 82)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 26)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= a_8_1 a_8_0))) true))))))) true) (summary_4_function_f__31_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_3 a_8_2))))


(assert
(forall ( (_34_1 Int) (_34_2 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_50_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__31_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) (= error_0 0))) (interface_0_C_50_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_20_function_g__49_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_21_g_48_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(block_20_function_g__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_1 a_37_1)))


(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_20_function_g__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_1 a_37_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_21_g_48_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_1 a_37_1))))


(declare-fun |block_22_return_function_g__49_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_21_g_48_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_1 a_37_1) (and (= _34_2 expr_46_0) (and (=> true (and (>= expr_46_0 0) (<= expr_46_0 1461501637330902918203684832716283019655932542975))) (and (= expr_46_0 a_37_2) (and (= a_37_2 expr_44_1) (and (=> true (and (>= expr_44_1 0) (<= expr_44_1 1461501637330902918203684832716283019655932542975))) (and (= expr_44_1 expr_43_1) (and (=> true (and (>= expr_39_0 0) (<= expr_39_0 1461501637330902918203684832716283019655932542975))) (and (= expr_39_0 a_37_1) (and (=> true (and (>= expr_43_1 0) (<= expr_43_1 1461501637330902918203684832716283019655932542975))) (and (= expr_43_1 expr_42_0) (and (=> true true) (and (= expr_42_0 0) (and (= _34_1 0) (and (= a_37_1 0) true))))))))))))))) true) (block_22_return_function_g__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_2 a_37_2))))


(declare-fun |block_23_return_ghost_g_47_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_23_return_ghost_g_47_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_2 a_37_2) (and (= _34_2 expr_46_0) (and (=> true (and (>= expr_46_0 0) (<= expr_46_0 1461501637330902918203684832716283019655932542975))) (and (= expr_46_0 a_37_2) (and (= a_37_2 expr_44_1) (and (=> true (and (>= expr_44_1 0) (<= expr_44_1 1461501637330902918203684832716283019655932542975))) (and (= expr_44_1 expr_43_1) (and (=> true (and (>= expr_39_0 0) (<= expr_39_0 1461501637330902918203684832716283019655932542975))) (and (= expr_39_0 a_37_1) (and (=> true (and (>= expr_43_1 0) (<= expr_43_1 1461501637330902918203684832716283019655932542975))) (and (= expr_43_1 expr_42_0) (and (=> true true) (and (= expr_42_0 0) (and (= _34_1 0) (and (= a_37_1 0) true))))))))))))))) true) (block_22_return_function_g__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_2 a_37_2))))


(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_22_return_function_g__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_1 a_37_1) true) true) (summary_5_function_g__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_1))))


(declare-fun |block_24_function_g__49_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(block_24_function_g__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_1 a_37_1)))


(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_24_function_g__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_1 a_37_1) (and (summary_5_function_g__49_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3 _34_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_6_function_g__49_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3 _34_1))))


(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_50_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_6_function_g__49_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _34_1) (= error_0 0))) (interface_0_C_50_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_25_C_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_26_C_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_26_C_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_27_C_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_26_C_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_27_C_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_27_C_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_25_C_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_28_C_50_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_28_C_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_28_C_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_25_C_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_28_C_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_25_C_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_50_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_50_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_50_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__31_50_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_8_0 state_1 a_8_1) (= error_0 1))) error_target_4_0)))


(assert
(forall ( (_34_0 Int) (_34_1 Int) (_34_2 Int) (a_37_0 Int) (a_37_1 Int) (a_37_2 Int) (a_8_0 Int) (a_8_1 Int) (a_8_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Bool) (expr_14_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_20_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_25_1 Bool) (expr_2_0 Bool) (expr_39_0 Int) (expr_42_0 Int) (expr_43_1 Int) (expr_44_1 Int) (expr_46_0 Int) (funds_2_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_address_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_4_0 false)))
(check-sat)