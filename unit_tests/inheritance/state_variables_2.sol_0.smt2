(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_Base1_3_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_Base1_3_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_Base1_3_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_1_Base1_3_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |interface_3_Base2_8_0| (Int |abi_type| |crypto_type| |state_type| Int Int ) Bool)
(declare-fun |nondet_interface_4_Base2_8_0| (Int Int |abi_type| |crypto_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_constructor_5_Base2_8_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (z_7_0 Int))
(=> (= error_0 0) (nondet_interface_4_Base2_8_0 error_0 this_0 abi_0 crypto_0 state_0 z_7_0 x_2_0 state_0 z_7_0 x_2_0))))


(declare-fun |interface_6_C_41_0| (Int |abi_type| |crypto_type| |state_type| Int Int ) Bool)
(declare-fun |nondet_interface_7_C_41_0| (Int Int |abi_type| |crypto_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_constructor_8_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (z_7_0 Int))
(=> (= error_0 0) (nondet_interface_7_C_41_0 error_0 this_0 abi_0 crypto_0 state_0 z_7_0 x_2_0 state_0 z_7_0 x_2_0))))


(declare-fun |summary_9_function_f__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |summary_10_function_f__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_12_0 Int) (y_12_1 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int))
(=> (and (and (nondet_interface_7_C_41_0 error_0 this_0 abi_0 crypto_0 state_0 z_7_0 x_2_0 state_1 z_7_1 x_2_1) true) (and (= error_0 0) (summary_10_function_f__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 z_7_1 x_2_1 y_12_0 state_2 z_7_2 x_2_2 y_12_1))) (nondet_interface_7_C_41_0 error_1 this_0 abi_0 crypto_0 state_0 z_7_0 x_2_0 state_2 z_7_2 x_2_2))))


(declare-fun |contract_initializer_11_Base1_3_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_12_Base1_3_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_12_0 Int) (y_12_1 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_0 x_2_0))) (contract_initializer_entry_12_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_0))))


(declare-fun |contract_initializer_after_init_13_Base1_3_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_12_0 Int) (y_12_1 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int))
(=> (and (and (contract_initializer_entry_12_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_13_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_12_0 Int) (y_12_1 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int))
(=> (and (and (contract_initializer_after_init_13_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_11_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_14_Base1_3_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_12_0 Int) (y_12_1 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_14_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_12_0 Int) (y_12_1 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int))
(=> (and (and (implicit_constructor_entry_14_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_11_Base1_3_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_2_Base1_3_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_12_0 Int) (y_12_1 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int))
(=> (and (and (implicit_constructor_entry_14_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_1 0) (and (contract_initializer_11_Base1_3_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))) true) (summary_constructor_2_Base1_3_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_12_0 Int) (y_12_1 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int))
(=> (and (and (summary_constructor_2_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_Base1_3_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |contract_initializer_15_Base2_8_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_16_Base2_8_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= z_7_0 z_7_0)) (= x_2_0 x_2_0))) (contract_initializer_entry_16_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_0 x_2_0))))


(declare-fun |contract_initializer_after_init_17_Base2_8_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (contract_initializer_entry_16_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) true) true) (contract_initializer_after_init_17_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (contract_initializer_after_init_17_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) true) true) (contract_initializer_15_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1))))


(declare-fun |contract_initializer_18_Base1_3_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_19_Base1_3_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_19_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_20_Base1_3_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (contract_initializer_entry_19_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_20_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (contract_initializer_after_init_20_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_18_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_21_Base2_8_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= z_7_1 z_7_0)) (= x_2_1 x_2_0))) (and (and true (= z_7_1 0)) (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_21_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (implicit_constructor_entry_21_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) (and (contract_initializer_18_Base1_3_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_5_Base2_8_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 z_7_0 x_2_0 z_7_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (implicit_constructor_entry_21_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) (and (contract_initializer_15_Base2_8_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 z_7_1 x_2_2 z_7_2 x_2_3) (and (= error_1 0) (and (contract_initializer_18_Base1_3_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))) (> error_2 0)) (summary_constructor_5_Base2_8_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 z_7_0 x_2_0 z_7_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (implicit_constructor_entry_21_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) (and (= error_2 0) (and (contract_initializer_15_Base2_8_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 z_7_1 x_2_2 z_7_2 x_2_3) (and (= error_1 0) (and (contract_initializer_18_Base1_3_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))))) true) (summary_constructor_5_Base2_8_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 z_7_0 x_2_0 z_7_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (summary_constructor_5_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_3_Base2_8_0 this_0 abi_0 crypto_0 state_1 z_7_1 x_2_1))))


(declare-fun |block_22_function_f__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_23_f_39_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(block_22_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_1 x_2_1 y_12_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (block_22_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_1 x_2_1 y_12_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= z_7_1 z_7_0)) (= x_2_1 x_2_0))) (and true (= y_12_1 y_12_0))) true)) true) (block_23_f_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_1 x_2_1 y_12_1))))


(declare-fun |block_24_return_function_f__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_25_function_f__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (block_23_f_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_1 x_2_1 y_12_1) (and (= expr_36_1 (< expr_34_0 expr_35_0)) (and (=> true true) (and (= expr_35_0 150) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 z_7_2) (and (= z_7_2 expr_31_1) (and (=> true (and (>= expr_31_1 0) (<= expr_31_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_31_1 expr_30_1) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 z_7_1) (and (=> true (and (>= expr_30_1 0) (<= expr_30_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_1 (+ expr_28_0 expr_29_0)) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 y_12_1) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_0 x_2_1) (and (=> true expr_24_1) (and (= expr_24_1 (< expr_22_0 expr_23_0)) (and (=> true true) (and (= expr_23_0 100) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 y_12_1) (and (=> true expr_18_1) (and (= expr_18_1 (< expr_16_0 expr_17_0)) (and (=> true true) (and (= expr_17_0 10) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_0 x_2_1) (and (and (>= y_12_1 0) (<= y_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))))))))))))))))))))) (and (not expr_36_1) (= error_1 1))) (block_25_function_f__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_2 x_2_1 y_12_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (block_25_function_f__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_2 x_2_1 y_12_1) (summary_9_function_f__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_2 x_2_1 y_12_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (block_23_f_39_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_1 x_2_1 y_12_1) (and (= error_1 error_0) (and (= expr_36_1 (< expr_34_0 expr_35_0)) (and (=> true true) (and (= expr_35_0 150) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 z_7_2) (and (= z_7_2 expr_31_1) (and (=> true (and (>= expr_31_1 0) (<= expr_31_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_31_1 expr_30_1) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 z_7_1) (and (=> true (and (>= expr_30_1 0) (<= expr_30_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_1 (+ expr_28_0 expr_29_0)) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 y_12_1) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_0 x_2_1) (and (=> true expr_24_1) (and (= expr_24_1 (< expr_22_0 expr_23_0)) (and (=> true true) (and (= expr_23_0 100) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 y_12_1) (and (=> true expr_18_1) (and (= expr_18_1 (< expr_16_0 expr_17_0)) (and (=> true true) (and (= expr_17_0 10) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_0 x_2_1) (and (and (>= y_12_1 0) (<= y_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))))))))))))))))))))))))) true) (block_24_return_function_f__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_2 x_2_1 y_12_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (block_24_return_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_1 x_2_1 y_12_1) true) true) (summary_9_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_1 x_2_1 y_12_1))))


(declare-fun |block_26_function_f__40_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(block_26_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_1 x_2_1 y_12_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (block_26_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_1 x_2_1 y_12_1) (and (summary_9_function_f__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 z_7_1 x_2_1 y_12_1 state_3 z_7_2 x_2_2 y_12_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3017696395)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 179)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 222)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 100)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 139)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= z_7_1 z_7_0)) (= x_2_1 x_2_0))) (and true (= y_12_1 y_12_0))) true))))))) true) (summary_10_function_f__40_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_3 z_7_2 x_2_2 y_12_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (interface_6_C_41_0 this_0 abi_0 crypto_0 state_0 z_7_0 x_2_0) true) (and (summary_10_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_1 x_2_1 y_12_1) (= error_0 0))) (interface_6_C_41_0 this_0 abi_0 crypto_0 state_1 z_7_1 x_2_1))))


(declare-fun |contract_initializer_27_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_28_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= z_7_1 z_7_0)) (= x_2_1 x_2_0))) (contract_initializer_entry_28_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1))))


(declare-fun |contract_initializer_after_init_29_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (contract_initializer_entry_28_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) true) true) (contract_initializer_after_init_29_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (contract_initializer_after_init_29_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) true) true) (contract_initializer_27_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1))))


(declare-fun |contract_initializer_30_Base2_8_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_31_Base2_8_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= z_7_1 z_7_0)) (= x_2_1 x_2_0))) (contract_initializer_entry_31_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1))))


(declare-fun |contract_initializer_after_init_32_Base2_8_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (contract_initializer_entry_31_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) true) true) (contract_initializer_after_init_32_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (contract_initializer_after_init_32_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) true) true) (contract_initializer_30_Base2_8_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1))))


(declare-fun |contract_initializer_33_Base1_3_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_34_Base1_3_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_34_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_35_Base1_3_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (contract_initializer_entry_34_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_35_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (contract_initializer_after_init_35_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_33_Base1_3_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_36_C_41_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= z_7_1 z_7_0)) (= x_2_1 x_2_0))) (and (and true (= z_7_1 0)) (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_36_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (implicit_constructor_entry_36_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) (and (contract_initializer_33_Base1_3_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_8_C_41_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 z_7_0 x_2_0 z_7_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (implicit_constructor_entry_36_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) (and (contract_initializer_30_Base2_8_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 z_7_1 x_2_2 z_7_2 x_2_3) (and (= error_1 0) (and (contract_initializer_33_Base1_3_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))) (> error_2 0)) (summary_constructor_8_C_41_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 z_7_0 x_2_0 z_7_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (implicit_constructor_entry_36_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) (and (contract_initializer_27_C_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 z_7_2 x_2_3 z_7_3 x_2_4) (and (= error_2 0) (and (contract_initializer_30_Base2_8_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 z_7_1 x_2_2 z_7_2 x_2_3) (and (= error_1 0) (and (contract_initializer_33_Base1_3_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))))) (> error_3 0)) (summary_constructor_8_C_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 z_7_0 x_2_0 z_7_3 x_2_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (implicit_constructor_entry_36_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) (and (= error_3 0) (and (contract_initializer_27_C_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 z_7_2 x_2_3 z_7_3 x_2_4) (and (= error_2 0) (and (contract_initializer_30_Base2_8_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 z_7_1 x_2_2 z_7_2 x_2_3) (and (= error_1 0) (and (contract_initializer_33_Base1_3_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))))))) true) (summary_constructor_8_C_41_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 z_7_0 x_2_0 z_7_3 x_2_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (summary_constructor_8_C_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_7_0 x_2_0 z_7_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_6_C_41_0 this_0 abi_0 crypto_0 state_1 z_7_1 x_2_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> (and (and (interface_6_C_41_0 this_0 abi_0 crypto_0 state_0 z_7_0 x_2_0) true) (and (summary_10_function_f__40_41_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 z_7_0 x_2_0 y_12_0 state_1 z_7_1 x_2_1 y_12_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Int) (expr_31_1 Int) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_12_0 Int) (y_12_1 Int) (y_12_2 Int) (y_12_3 Int) (y_12_4 Int) (y_12_5 Int) (z_7_0 Int) (z_7_1 Int) (z_7_2 Int) (z_7_3 Int))
(=> error_target_3_0 false)))
(check-sat)