(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_I1_1_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_I1_1_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_I1_1_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_I1_1_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |interface_3_I2_5_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_4_I2_5_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_5_I2_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_4_I2_5_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_6_function_f__4_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_7_function_f__4_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_4_I2_5_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_7_function_f__4_5_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_4_I2_5_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_8_I3_16_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_9_I3_16_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_10_I3_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_1 0) (nondet_interface_9_I3_16_0 error_1 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_11_function_f__8_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_12_function_f__8_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_9_I3_16_0 error_1 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_1 0) (summary_12_function_f__8_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_9_I3_16_0 error_2 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_13_function_g__15_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_14_function_g__15_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_12_0 Int) (_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_9_I3_16_0 error_2 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_2 0) (summary_14_function_g__15_16_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 _10_0 _12_0 state_2 _10_1 _12_1))) (nondet_interface_9_I3_16_0 error_3 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_15_C_98_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_16_C_98_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_17_C_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_12_0 Int) (_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_3 0) (nondet_interface_16_C_98_0 error_3 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_18_function_f__65_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_19_function_f__65_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_12_0 Int) (_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_16_C_98_0 error_3 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_3 0) (summary_19_function_f__65_98_0 error_4 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_16_C_98_0 error_4 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_20_function_g__81_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_21_function_g__81_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_12_0 Int) (_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_16_C_98_0 error_4 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_4 0) (summary_21_function_g__81_98_0 error_5 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_16_C_98_0 error_5 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_22_function_h__97_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_23_function_h__97_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_12_0 Int) (_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_16_C_98_0 error_5 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_5 0) (summary_23_function_h__97_98_0 error_6 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_16_C_98_0 error_6 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |contract_initializer_24_I1_1_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_25_I1_1_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_12_0 Int) (_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_25_I1_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_26_I1_1_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_12_0 Int) (_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_25_I1_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_26_I1_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_12_0 Int) (_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_26_I1_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_24_I1_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_27_I1_1_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_12_0 Int) (_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_27_I1_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_12_0 Int) (_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_27_I1_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_24_I1_1_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_I1_1_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_12_0 Int) (_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_27_I1_1_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_24_I1_1_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_I1_1_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and true (= error_0 0)) (summary_6_function_f__4_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_28_I2_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_29_I2_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_29_I2_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_30_I2_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_29_I2_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_30_I2_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_30_I2_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_28_I2_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_31_I2_5_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_31_I2_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_31_I2_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_28_I2_5_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_5_I2_5_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_31_I2_5_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_28_I2_5_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_5_I2_5_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and true (= error_0 0)) (summary_11_function_f__8_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and true (= error_0 0)) (summary_13_function_g__15_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 _10_0 _12_0 state_1 _10_5 _12_5))))


(declare-fun |contract_initializer_32_I3_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_33_I3_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_33_I3_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_34_I3_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_33_I3_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_34_I3_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_34_I3_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_32_I3_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_35_I3_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_35_I3_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_35_I3_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_32_I3_16_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_10_I3_16_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_35_I3_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_32_I3_16_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_10_I3_16_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(declare-fun |block_36_function_f__65_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_37_f_64_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_36_function_f__65_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_36_function_f__65_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_37_f_64_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_38_return_function_f__65_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_39_function_f__65_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_37_f_64_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_25_1 (= expr_23_1 expr_24_0)) (and (=> true true) (and (= expr_24_0 0) (and (=> true (and (>= expr_23_1 0) (<= expr_23_1 4294967295))) (and (= expr_23_1 0) true)))))) (and (not expr_25_1) (= error_1 1))) (block_39_function_f__65_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_39_function_f__65_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_18_function_f__65_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_40_function_f__65_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_37_f_64_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_34_1 (not (= expr_32_1 expr_33_0))) (and (=> true true) (and (= expr_33_0 0) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 4294967295))) (and (= expr_32_1 638722032) (and (= error_1 error_0) (and (= expr_25_1 (= expr_23_1 expr_24_0)) (and (=> true true) (and (= expr_24_0 0) (and (=> true (and (>= expr_23_1 0) (<= expr_23_1 4294967295))) (and (= expr_23_1 0) true)))))))))))) (and (not expr_34_1) (= error_2 2))) (block_40_function_f__65_98_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_40_function_f__65_98_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_18_function_f__65_98_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_41_function_f__65_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_37_f_64_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_43_1 (= expr_41_1 expr_42_0)) (and (=> true true) (and (= expr_42_0 638722032) (and (=> true (and (>= expr_41_1 0) (<= expr_41_1 4294967295))) (and (= expr_41_1 638722032) (and (= error_2 error_1) (and (= expr_34_1 (not (= expr_32_1 expr_33_0))) (and (=> true true) (and (= expr_33_0 0) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 4294967295))) (and (= expr_32_1 638722032) (and (= error_1 error_0) (and (= expr_25_1 (= expr_23_1 expr_24_0)) (and (=> true true) (and (= expr_24_0 0) (and (=> true (and (>= expr_23_1 0) (<= expr_23_1 4294967295))) (and (= expr_23_1 0) true)))))))))))))))))) (and (not expr_43_1) (= error_3 3))) (block_41_function_f__65_98_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_41_function_f__65_98_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_18_function_f__65_98_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_42_function_f__65_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_37_f_64_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_52_1 (not (= expr_50_1 expr_51_0))) (and (=> true true) (and (= expr_51_0 0) (and (=> true (and (>= expr_50_1 0) (<= expr_50_1 4294967295))) (and (= expr_50_1 638722032) (and (= error_3 error_2) (and (= expr_43_1 (= expr_41_1 expr_42_0)) (and (=> true true) (and (= expr_42_0 638722032) (and (=> true (and (>= expr_41_1 0) (<= expr_41_1 4294967295))) (and (= expr_41_1 638722032) (and (= error_2 error_1) (and (= expr_34_1 (not (= expr_32_1 expr_33_0))) (and (=> true true) (and (= expr_33_0 0) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 4294967295))) (and (= expr_32_1 638722032) (and (= error_1 error_0) (and (= expr_25_1 (= expr_23_1 expr_24_0)) (and (=> true true) (and (= expr_24_0 0) (and (=> true (and (>= expr_23_1 0) (<= expr_23_1 4294967295))) (and (= expr_23_1 0) true)))))))))))))))))))))))) (and (not expr_52_1) (= error_4 4))) (block_42_function_f__65_98_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_42_function_f__65_98_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_18_function_f__65_98_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_43_function_f__65_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_37_f_64_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_61_1 (= expr_59_1 expr_60_0)) (and (=> true true) (and (= expr_60_0 2183877062) (and (=> true (and (>= expr_59_1 0) (<= expr_59_1 4294967295))) (and (= expr_59_1 2183877062) (and (= error_4 error_3) (and (= expr_52_1 (not (= expr_50_1 expr_51_0))) (and (=> true true) (and (= expr_51_0 0) (and (=> true (and (>= expr_50_1 0) (<= expr_50_1 4294967295))) (and (= expr_50_1 638722032) (and (= error_3 error_2) (and (= expr_43_1 (= expr_41_1 expr_42_0)) (and (=> true true) (and (= expr_42_0 638722032) (and (=> true (and (>= expr_41_1 0) (<= expr_41_1 4294967295))) (and (= expr_41_1 638722032) (and (= error_2 error_1) (and (= expr_34_1 (not (= expr_32_1 expr_33_0))) (and (=> true true) (and (= expr_33_0 0) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 4294967295))) (and (= expr_32_1 638722032) (and (= error_1 error_0) (and (= expr_25_1 (= expr_23_1 expr_24_0)) (and (=> true true) (and (= expr_24_0 0) (and (=> true (and (>= expr_23_1 0) (<= expr_23_1 4294967295))) (and (= expr_23_1 0) true)))))))))))))))))))))))))))))) (and (not expr_61_1) (= error_5 5))) (block_43_function_f__65_98_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_43_function_f__65_98_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_18_function_f__65_98_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_37_f_64_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_5 error_4) (and (= expr_61_1 (= expr_59_1 expr_60_0)) (and (=> true true) (and (= expr_60_0 2183877062) (and (=> true (and (>= expr_59_1 0) (<= expr_59_1 4294967295))) (and (= expr_59_1 2183877062) (and (= error_4 error_3) (and (= expr_52_1 (not (= expr_50_1 expr_51_0))) (and (=> true true) (and (= expr_51_0 0) (and (=> true (and (>= expr_50_1 0) (<= expr_50_1 4294967295))) (and (= expr_50_1 638722032) (and (= error_3 error_2) (and (= expr_43_1 (= expr_41_1 expr_42_0)) (and (=> true true) (and (= expr_42_0 638722032) (and (=> true (and (>= expr_41_1 0) (<= expr_41_1 4294967295))) (and (= expr_41_1 638722032) (and (= error_2 error_1) (and (= expr_34_1 (not (= expr_32_1 expr_33_0))) (and (=> true true) (and (= expr_33_0 0) (and (=> true (and (>= expr_32_1 0) (<= expr_32_1 4294967295))) (and (= expr_32_1 638722032) (and (= error_1 error_0) (and (= expr_25_1 (= expr_23_1 expr_24_0)) (and (=> true true) (and (= expr_24_0 0) (and (=> true (and (>= expr_23_1 0) (<= expr_23_1 4294967295))) (and (= expr_23_1 0) true))))))))))))))))))))))))))))))) true) (block_38_return_function_f__65_98_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_38_return_function_f__65_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_18_function_f__65_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_44_function_f__65_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_44_function_f__65_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_44_function_f__65_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_18_function_f__65_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_6_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_6_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_6_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_6_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_19_function_f__65_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_15_C_98_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_19_function_f__65_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_15_C_98_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_45_function_g__81_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_46_g_80_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_45_function_g__81_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_45_function_g__81_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_46_g_80_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_47_return_function_g__81_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_48_function_g__81_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_46_g_80_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_77_1 (= expr_72_1 expr_76_1)) (and (=> true (and (>= expr_76_1 0) (<= expr_76_1 4294967295))) (and (= expr_76_1 638722032) (and (=> true (and (>= expr_72_1 0) (<= expr_72_1 4294967295))) (and (= expr_72_1 0) true)))))) (and (not expr_77_1) (= error_1 7))) (block_48_function_g__81_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_48_function_g__81_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_20_function_g__81_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_46_g_80_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 error_0) (and (= expr_77_1 (= expr_72_1 expr_76_1)) (and (=> true (and (>= expr_76_1 0) (<= expr_76_1 4294967295))) (and (= expr_76_1 638722032) (and (=> true (and (>= expr_72_1 0) (<= expr_72_1 4294967295))) (and (= expr_72_1 0) true))))))) true) (block_47_return_function_g__81_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_47_return_function_g__81_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_20_function_g__81_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_49_function_g__81_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (funds_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_49_function_g__81_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_49_function_g__81_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_20_function_g__81_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_8_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_8_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_8_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_8_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_21_function_g__81_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_15_C_98_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_21_function_g__81_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_15_C_98_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_50_function_h__97_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_51_h_96_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_50_function_h__97_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_50_function_h__97_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_51_h_96_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_52_return_function_h__97_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_53_function_h__97_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_51_h_96_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_93_1 (= expr_88_1 expr_92_1)) (and (=> true (and (>= expr_92_1 0) (<= expr_92_1 4294967295))) (and (= expr_92_1 2183877062) (and (=> true (and (>= expr_88_1 0) (<= expr_88_1 4294967295))) (and (= expr_88_1 638722032) true)))))) (and (not expr_93_1) (= error_1 9))) (block_53_function_h__97_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_53_function_h__97_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_22_function_h__97_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_51_h_96_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 error_0) (and (= expr_93_1 (= expr_88_1 expr_92_1)) (and (=> true (and (>= expr_92_1 0) (<= expr_92_1 4294967295))) (and (= expr_92_1 2183877062) (and (=> true (and (>= expr_88_1 0) (<= expr_88_1 4294967295))) (and (= expr_88_1 638722032) true))))))) true) (block_52_return_function_h__97_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_52_return_function_h__97_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_22_function_h__97_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_54_function_h__97_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_54_function_h__97_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_54_function_h__97_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_22_function_h__97_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_10_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_10_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_10_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_10_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3100234597)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 184)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 201)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 211)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 101)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_23_function_h__97_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_15_C_98_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_23_function_h__97_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_15_C_98_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_55_C_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_56_C_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_56_C_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_57_C_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_56_C_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_57_C_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_57_C_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_55_C_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_58_C_98_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_58_C_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_58_C_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_55_C_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_17_C_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_58_C_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_55_C_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_17_C_98_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_17_C_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_15_C_98_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_11_0| () Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_10_8 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (_12_8 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_15_C_98_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_19_function_f__65_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 1))) error_target_11_0)))


(declare-fun |error_target_12_0| () Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_10_8 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (_12_8 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_15_C_98_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_19_function_f__65_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 2))) error_target_12_0)))


(declare-fun |error_target_13_0| () Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_10_8 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (_12_8 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_15_C_98_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_19_function_f__65_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 3))) error_target_13_0)))


(declare-fun |error_target_14_0| () Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_10_8 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (_12_8 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_15_C_98_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_19_function_f__65_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 4))) error_target_14_0)))


(declare-fun |error_target_15_0| () Bool)
(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_10_8 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (_12_8 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_15_C_98_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_19_function_f__65_98_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 5))) error_target_15_0)))


(assert
(forall ( (_10_0 Int) (_10_1 Int) (_10_2 Int) (_10_3 Int) (_10_4 Int) (_10_5 Int) (_10_6 Int) (_10_7 Int) (_10_8 Int) (_12_0 Int) (_12_1 Int) (_12_2 Int) (_12_3 Int) (_12_4 Int) (_12_5 Int) (_12_6 Int) (_12_7 Int) (_12_8 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_32_1 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_41_1 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_50_1 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_59_1 Int) (expr_60_0 Int) (expr_61_1 Bool) (expr_72_1 Int) (expr_76_1 Int) (expr_77_1 Bool) (expr_88_1 Int) (expr_92_1 Int) (expr_93_1 Bool) (funds_10_0 Int) (funds_6_0 Int) (funds_8_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_15_0 false)))
(check-sat)