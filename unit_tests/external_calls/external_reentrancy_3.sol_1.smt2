(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_D_5_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_D_5_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_D_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_D_5_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_d__4_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_4_function_d__4_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_D_5_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_d__4_5_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_D_5_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_5_A_25_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_6_A_25_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_7_A_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int))
(=> (= error_1 0) (nondet_interface_6_A_25_0 error_1 this_0 abi_0 crypto_0 state_0 x_8_0 state_0 x_8_0))))


(declare-fun |summary_8_function_f__24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_9_function_f__24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (nondet_interface_6_A_25_0 error_1 this_0 abi_0 crypto_0 state_0 x_8_0 state_1 x_8_1) true) (and (= error_1 0) (summary_9_function_f__24_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_8_1 state_2 x_8_2))) (nondet_interface_6_A_25_0 error_2 this_0 abi_0 crypto_0 state_0 x_8_0 state_2 x_8_2))))


(declare-fun |interface_10_C_65_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_11_C_65_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_12_C_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (= error_2 0) (nondet_interface_11_C_65_0 error_2 this_0 abi_0 crypto_0 state_0 x_8_0 state_0 x_8_0))))


(declare-fun |summary_13_function_f__24_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_14_constructor_35_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_15_function_call__47_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_16_function_call__47_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (nondet_interface_11_C_65_0 error_2 this_0 abi_0 crypto_0 state_0 x_8_0 state_1 x_8_1) true) (and (= error_2 0) (summary_16_function_call__47_65_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 x_8_1 d_38_0 state_2 x_8_2 d_38_1))) (nondet_interface_11_C_65_0 error_3 this_0 abi_0 crypto_0 state_0 x_8_0 state_2 x_8_2))))


(declare-fun |summary_17_function_f__64_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_18_function_f__64_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (nondet_interface_11_C_65_0 error_3 this_0 abi_0 crypto_0 state_0 x_8_0 state_1 x_8_1) true) (and (= error_3 0) (summary_18_function_f__64_65_0 error_4 this_0 abi_0 crypto_0 tx_0 state_1 x_8_1 state_2 x_8_2))) (nondet_interface_11_C_65_0 error_4 this_0 abi_0 crypto_0 state_0 x_8_0 state_2 x_8_2))))


(declare-fun |block_19_function_d__4_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_20_d_3_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(block_19_function_d__4_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_19_function_d__4_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_20_d_3_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_21_return_function_d__4_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_20_d_3_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (block_21_return_function_d__4_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (block_21_return_function_d__4_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_3_function_d__4_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_22_D_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_23_D_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_23_D_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_24_D_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (contract_initializer_entry_23_D_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_24_D_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (contract_initializer_after_init_24_D_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_22_D_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_25_D_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_25_D_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (implicit_constructor_entry_25_D_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_22_D_5_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_D_5_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int))
(=> (and (and (implicit_constructor_entry_25_D_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_22_D_5_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_D_5_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(declare-fun |block_26_function_f__24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_27_f_23_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(block_26_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_26_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) true) true)) true) (block_27_f_23_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(declare-fun |block_28_return_function_f__24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_29_function_f__24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_27_f_23_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (= expr_14_1 (= expr_12_0 expr_13_0)) (and (=> true true) (and (= expr_13_0 0) (and (=> true (and (>= expr_12_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_12_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_12_0 x_8_1) true)))))) (and (not expr_14_1) (= error_1 1))) (block_29_function_f__24_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (block_29_function_f__24_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (summary_8_function_f__24_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(declare-fun |block_30_function_f__24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_27_f_23_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (= expr_20_1 (= expr_18_0 expr_19_0)) (and (=> true true) (and (= expr_19_0 1) (and (=> true (and (>= expr_18_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_18_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_18_0 x_8_1) (and (= error_1 error_0) (and (= expr_14_1 (= expr_12_0 expr_13_0)) (and (=> true true) (and (= expr_13_0 0) (and (=> true (and (>= expr_12_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_12_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_12_0 x_8_1) true)))))))))))) (and (not expr_20_1) (= error_2 2))) (block_30_function_f__24_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (block_30_function_f__24_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (summary_8_function_f__24_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_27_f_23_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (= error_2 error_1) (and (= expr_20_1 (= expr_18_0 expr_19_0)) (and (=> true true) (and (= expr_19_0 1) (and (=> true (and (>= expr_18_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_18_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_18_0 x_8_1) (and (= error_1 error_0) (and (= expr_14_1 (= expr_12_0 expr_13_0)) (and (=> true true) (and (= expr_13_0 0) (and (=> true (and (>= expr_12_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_12_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_12_0 x_8_1) true))))))))))))) true) (block_28_return_function_f__24_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_28_return_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) true) true) (summary_8_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(declare-fun |block_31_function_f__24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(block_31_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_31_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (summary_8_function_f__24_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_8_1 state_3 x_8_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) true) true))))))) true) (summary_9_function_f__24_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_3 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (interface_5_A_25_0 this_0 abi_0 crypto_0 state_0 x_8_0) true) (and (summary_9_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (= error_0 0))) (interface_5_A_25_0 this_0 abi_0 crypto_0 state_1 x_8_1))))


(declare-fun |contract_initializer_32_A_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_33_A_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) (contract_initializer_entry_33_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1))))


(declare-fun |contract_initializer_after_init_34_A_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (contract_initializer_entry_33_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1) (and (= x_8_2 expr_7_0) (and (=> true true) (and (= expr_7_0 0) true)))) true) (contract_initializer_after_init_34_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (contract_initializer_after_init_34_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1) true) true) (contract_initializer_32_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1))))


(declare-fun |implicit_constructor_entry_35_A_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) (and true (= x_8_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_35_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (implicit_constructor_entry_35_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1) (and (contract_initializer_32_A_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_8_1 x_8_2) true)) (> error_1 0)) (summary_constructor_7_A_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_8_0 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (implicit_constructor_entry_35_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1) (and (= error_1 0) (and (contract_initializer_32_A_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_8_1 x_8_2) true))) true) (summary_constructor_7_A_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_8_0 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (summary_constructor_7_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_5_A_25_0 this_0 abi_0 crypto_0 state_1 x_8_1))))


(declare-fun |block_36_function_f__24_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_37_f_23_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(block_36_function_f__24_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_36_function_f__24_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) true) true)) true) (block_37_f_23_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(declare-fun |block_38_return_function_f__24_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_39_function_f__24_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_37_f_23_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (= expr_14_1 (= expr_12_0 expr_13_0)) (and (=> true true) (and (= expr_13_0 0) (and (=> true (and (>= expr_12_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_12_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_12_0 x_8_1) true)))))) (and (not expr_14_1) (= error_1 4))) (block_39_function_f__24_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (block_39_function_f__24_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (summary_13_function_f__24_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(declare-fun |block_40_function_f__24_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_37_f_23_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (= expr_20_1 (= expr_18_0 expr_19_0)) (and (=> true true) (and (= expr_19_0 1) (and (=> true (and (>= expr_18_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_18_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_18_0 x_8_1) (and (= error_1 error_0) (and (= expr_14_1 (= expr_12_0 expr_13_0)) (and (=> true true) (and (= expr_13_0 0) (and (=> true (and (>= expr_12_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_12_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_12_0 x_8_1) true)))))))))))) (and (not expr_20_1) (= error_2 5))) (block_40_function_f__24_65_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (block_40_function_f__24_65_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (summary_13_function_f__24_65_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_37_f_23_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (= error_2 error_1) (and (= expr_20_1 (= expr_18_0 expr_19_0)) (and (=> true true) (and (= expr_19_0 1) (and (=> true (and (>= expr_18_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_18_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_18_0 x_8_1) (and (= error_1 error_0) (and (= expr_14_1 (= expr_12_0 expr_13_0)) (and (=> true true) (and (= expr_13_0 0) (and (=> true (and (>= expr_12_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_12_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_12_0 x_8_1) true))))))))))))) true) (block_38_return_function_f__24_65_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_38_return_function_f__24_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) true) true) (summary_13_function_f__24_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(declare-fun |block_41_function_call__47_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_42_call_46_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(block_41_function_call__47_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_1 x_8_1 d_38_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_41_function_call__47_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_1 x_8_1 d_38_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) (and true (= d_38_1 d_38_0))) true)) true) (block_42_call_46_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_1 x_8_1 d_38_1))))


(declare-fun |block_43_return_function_call__47_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |nondet_call_44_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (nondet_interface_11_C_65_0 error_1 this_0 abi_0 crypto_0 state_1 x_8_1 state_2 x_8_2) (nondet_call_44_0 error_1 this_0 abi_0 crypto_0 state_1 x_8_1 state_2 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_42_call_46_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_1 x_8_1 d_38_1) (and (nondet_call_44_0 error_1 this_0 abi_0 crypto_0 state_1 x_8_1 state_2 x_8_2) (and (=> true true) (and (= expr_41_0 d_38_1) (and (and (>= d_38_1 0) (<= d_38_1 1461501637330902918203684832716283019655932542975)) true))))) (> error_1 0)) (summary_15_function_call__47_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_2 x_8_2 d_38_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_42_call_46_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_1 x_8_1 d_38_1) (and (= error_1 0) (and (nondet_call_44_0 error_1 this_0 abi_0 crypto_0 state_1 x_8_1 state_2 x_8_2) (and (=> true true) (and (= expr_41_0 d_38_1) (and (and (>= d_38_1 0) (<= d_38_1 1461501637330902918203684832716283019655932542975)) true)))))) true) (block_43_return_function_call__47_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_2 x_8_2 d_38_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_43_return_function_call__47_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_1 x_8_1 d_38_1) true) true) (summary_15_function_call__47_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_1 x_8_1 d_38_1))))


(declare-fun |block_45_function_call__47_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(block_45_function_call__47_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_1 x_8_1 d_38_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_45_function_call__47_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_1 x_8_1 d_38_1) (and (summary_15_function_call__47_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_8_1 d_38_1 state_3 x_8_2 d_38_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_6_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_6_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_6_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_6_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 4115870379)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 245)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 83)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 50)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 171)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) (and true (= d_38_1 d_38_0))) true))))))) true) (summary_16_function_call__47_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_3 x_8_2 d_38_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (interface_10_C_65_0 this_0 abi_0 crypto_0 state_0 x_8_0) true) (and (summary_16_function_call__47_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 d_38_0 state_1 x_8_1 d_38_1) (= error_0 0))) (interface_10_C_65_0 this_0 abi_0 crypto_0 state_1 x_8_1))))


(declare-fun |block_46_function_f__64_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_47_f_63_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(block_46_function_f__64_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_46_function_f__64_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) true) true)) true) (block_47_f_63_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(declare-fun |block_48_return_function_f__64_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_49_function_f__64_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_47_f_63_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (= expr_54_1 (= expr_52_0 expr_53_0)) (and (=> true true) (and (= expr_53_0 1) (and (=> true (and (>= expr_52_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_52_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_52_0 x_8_1) true)))))) (and (not expr_54_1) (= error_1 7))) (block_49_function_f__64_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (block_49_function_f__64_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (summary_17_function_f__64_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(declare-fun |block_50_function_f__64_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_47_f_63_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (= expr_60_1 (= expr_58_0 expr_59_0)) (and (=> true true) (and (= expr_59_0 0) (and (=> true (and (>= expr_58_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_58_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_58_0 x_8_1) (and (= error_1 error_0) (and (= expr_54_1 (= expr_52_0 expr_53_0)) (and (=> true true) (and (= expr_53_0 1) (and (=> true (and (>= expr_52_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_52_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_52_0 x_8_1) true)))))))))))) (and (not expr_60_1) (= error_2 8))) (block_50_function_f__64_65_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (block_50_function_f__64_65_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (summary_17_function_f__64_65_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_47_f_63_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (= error_2 error_1) (and (= expr_60_1 (= expr_58_0 expr_59_0)) (and (=> true true) (and (= expr_59_0 0) (and (=> true (and (>= expr_58_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_58_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_58_0 x_8_1) (and (= error_1 error_0) (and (= expr_54_1 (= expr_52_0 expr_53_0)) (and (=> true true) (and (= expr_53_0 1) (and (=> true (and (>= expr_52_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_52_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_52_0 x_8_1) true))))))))))))) true) (block_48_return_function_f__64_65_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_48_return_function_f__64_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) true) true) (summary_17_function_f__64_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(declare-fun |block_51_function_f__64_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(block_51_function_f__64_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_51_function_f__64_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (summary_17_function_f__64_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_8_1 state_3 x_8_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_9_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_9_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_9_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_9_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) true) true))))))) true) (summary_18_function_f__64_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_3 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (interface_10_C_65_0 this_0 abi_0 crypto_0 state_0 x_8_0) true) (and (summary_18_function_f__64_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (= error_0 0))) (interface_10_C_65_0 this_0 abi_0 crypto_0 state_1 x_8_1))))


(declare-fun |block_52_constructor_35_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_53__34_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(block_52_constructor_35_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_52_constructor_35_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) true) true)) true) (block_53__34_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(declare-fun |block_54_return_constructor_35_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_53__34_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (= x_8_2 expr_32_1) (and (=> true (and (>= expr_32_1 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_32_1 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_32_1 expr_31_0) (and (=> true (and (>= expr_30_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_30_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_30_0 x_8_1) (and (=> true true) (and (= expr_31_0 1) true)))))))) true) (block_54_return_constructor_35_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (block_54_return_constructor_35_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) true) true) (summary_14_constructor_35_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(declare-fun |contract_initializer_55_C_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_56_C_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) true) (contract_initializer_entry_56_C_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(declare-fun |contract_initializer_after_init_57_C_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (contract_initializer_entry_56_C_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) true) true) (contract_initializer_after_init_57_C_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (contract_initializer_after_init_57_C_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (summary_14_constructor_35_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_8_1 state_2 x_8_2) true)) (> error_1 0)) (contract_initializer_55_C_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_2 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (contract_initializer_after_init_57_C_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (= error_1 0) (and (summary_14_constructor_35_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_8_1 state_2 x_8_2) true))) true) (contract_initializer_55_C_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_2 x_8_2))))


(declare-fun |contract_initializer_58_A_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_59_A_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_8_2 x_8_0))) (contract_initializer_entry_59_A_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_8_0 x_8_2))))


(declare-fun |contract_initializer_after_init_60_A_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (contract_initializer_entry_59_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1) (and (= x_8_2 expr_7_0) (and (=> true true) (and (= expr_7_0 0) true)))) true) (contract_initializer_after_init_60_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (contract_initializer_after_init_60_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1) true) true) (contract_initializer_58_A_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_8_0 x_8_1))))


(declare-fun |implicit_constructor_entry_61_C_65_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_8_1 x_8_0))) true) (and true (= x_8_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_61_C_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (implicit_constructor_entry_61_C_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (contract_initializer_58_A_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_8_1 x_8_2) true)) (> error_1 0)) (summary_constructor_12_C_65_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_2 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (implicit_constructor_entry_61_C_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (contract_initializer_55_C_65_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_8_2 state_3 x_8_3) (and (= error_1 0) (and (contract_initializer_58_A_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_8_1 x_8_2) true)))) (> error_2 0)) (summary_constructor_12_C_65_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_3 x_8_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (implicit_constructor_entry_61_C_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (and (= error_2 0) (and (contract_initializer_55_C_65_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_8_2 state_3 x_8_3) (and (= error_1 0) (and (contract_initializer_58_A_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_8_1 x_8_2) true))))) true) (summary_constructor_12_C_65_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_3 x_8_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (summary_constructor_12_C_65_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_10_C_65_0 this_0 abi_0 crypto_0 state_1 x_8_1))))


(declare-fun |error_target_10_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (interface_5_A_25_0 this_0 abi_0 crypto_0 state_0 x_8_0) true) (and (summary_9_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (= error_0 1))) error_target_10_0)))


(declare-fun |error_target_11_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (interface_5_A_25_0 this_0 abi_0 crypto_0 state_0 x_8_0) true) (and (summary_9_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (= error_0 2))) error_target_11_0)))


(declare-fun |error_target_12_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (interface_5_A_25_0 this_0 abi_0 crypto_0 state_0 x_8_0) true) (and (summary_9_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (= error_0 4))) error_target_12_0)))


(declare-fun |error_target_13_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> (and (and (interface_5_A_25_0 this_0 abi_0 crypto_0 state_0 x_8_0) true) (and (summary_9_function_f__24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_8_0 state_1 x_8_1) (= error_0 5))) error_target_13_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_38_0 Int) (d_38_1 Int) (d_38_2 Int) (d_38_3 Int) (d_38_4 Int) (d_38_5 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_0 Int) (expr_19_0 Int) (expr_20_1 Bool) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Int) (expr_41_0 Int) (expr_44_1 |tuple()|) (expr_52_0 Int) (expr_53_0 Int) (expr_54_1 Bool) (expr_58_0 Int) (expr_59_0 Int) (expr_60_1 Bool) (expr_7_0 Int) (funds_3_0 Int) (funds_6_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (x_8_3 Int))
(=> error_target_13_0 false)))
(check-sat)