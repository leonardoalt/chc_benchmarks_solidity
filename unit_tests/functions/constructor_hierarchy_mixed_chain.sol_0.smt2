(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_F_11_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_F_11_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_F_11_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_3_constructor_10_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_4_E_14_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_5_E_14_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_6_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_5_E_14_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_7_constructor_10_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_8_D_25_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_9_D_25_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_10_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_9_D_25_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_11_constructor_10_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_12_constructor_24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_13_C_28_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_14_C_28_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_15_C_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_14_C_28_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_16_constructor_10_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_17_constructor_24_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_18_B_39_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_19_B_39_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_20_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_19_B_39_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_21_constructor_10_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_22_constructor_24_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_23_constructor_38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_24_A_60_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_25_A_60_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_26_A_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_25_A_60_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_27_constructor_10_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_28_constructor_24_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_29_constructor_38_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_30_constructor_59_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_31_constructor_10_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_32__9_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int))
(block_31_constructor_10_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int))
(=> (and (and (block_31_constructor_10_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_32__9_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_33_return_constructor_10_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int))
(=> (and (and (block_32__9_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_33_return_constructor_10_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int))
(=> (and (and (block_33_return_constructor_10_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_3_constructor_10_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_34_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_35_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_35_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_36_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int))
(=> (and (and (contract_initializer_entry_35_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_36_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int))
(=> (and (and (contract_initializer_after_init_36_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_3_constructor_10_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_34_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int))
(=> (and (and (contract_initializer_after_init_36_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_3_constructor_10_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_34_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |implicit_constructor_entry_37_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) true) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_37_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int))
(=> (and (and (implicit_constructor_entry_37_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_34_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (summary_constructor_2_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int))
(=> (and (and (implicit_constructor_entry_37_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (contract_initializer_34_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (summary_constructor_2_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int))
(=> (and (and (summary_constructor_2_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_F_11_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |contract_initializer_38_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_39_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_0 a_2_0))) (contract_initializer_entry_39_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_0))))


(declare-fun |contract_initializer_after_init_40_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (contract_initializer_entry_39_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_40_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (contract_initializer_after_init_40_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_38_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_41_constructor_10_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_42__9_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(block_41_constructor_10_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (block_41_constructor_10_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_42__9_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_43_return_constructor_10_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (block_42__9_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_43_return_constructor_10_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (block_43_return_constructor_10_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_7_constructor_10_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_44_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_45_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_45_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_46_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (contract_initializer_entry_45_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_46_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (contract_initializer_after_init_46_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_7_constructor_10_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_44_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (contract_initializer_after_init_46_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_7_constructor_10_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_44_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |implicit_constructor_entry_47_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_47_E_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (implicit_constructor_entry_47_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_44_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (summary_constructor_6_E_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (implicit_constructor_entry_47_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_38_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_44_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))) (> error_2 0)) (summary_constructor_6_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 a_2_0 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (implicit_constructor_entry_47_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (= error_2 0) (and (contract_initializer_38_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_44_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))))) true) (summary_constructor_6_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 a_2_0 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int))
(=> (and (and (summary_constructor_6_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_4_E_14_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |block_48_constructor_24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_49__23_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(block_48_constructor_24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (block_48_constructor_24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_49__23_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_50_return_constructor_24_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (block_49__23_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_21_1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_1 expr_20_0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 a_2_1) (and (=> true true) (and (= expr_20_0 3) true)))))))) true) (block_50_return_constructor_24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (block_50_return_constructor_24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_12_constructor_24_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_51_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_52_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_52_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_53_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (contract_initializer_entry_52_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_53_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (contract_initializer_after_init_53_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_12_constructor_24_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_51_D_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (contract_initializer_after_init_53_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_12_constructor_24_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_51_D_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |contract_initializer_54_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_55_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_55_E_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_56_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (contract_initializer_entry_55_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_56_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (contract_initializer_after_init_56_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_54_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_57_constructor_10_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_58__9_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(block_57_constructor_10_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (block_57_constructor_10_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_58__9_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_59_return_constructor_10_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (block_58__9_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_59_return_constructor_10_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (block_59_return_constructor_10_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_11_constructor_10_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_60_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_61_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_61_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_62_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (contract_initializer_entry_61_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_62_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (contract_initializer_after_init_62_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_11_constructor_10_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_60_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (contract_initializer_after_init_62_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_11_constructor_10_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_60_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |implicit_constructor_entry_63_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) true) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_63_D_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (implicit_constructor_entry_63_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_60_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (summary_constructor_10_D_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (implicit_constructor_entry_63_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_54_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_60_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))) (> error_2 0)) (summary_constructor_10_D_25_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (implicit_constructor_entry_63_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_51_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_54_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_60_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))) (> error_3 0)) (summary_constructor_10_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_4))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (implicit_constructor_entry_63_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_3 0) (and (contract_initializer_51_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_54_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_60_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))))))) true) (summary_constructor_10_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_4))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int))
(=> (and (and (summary_constructor_10_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_8_D_25_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |contract_initializer_64_C_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_65_C_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_0 a_2_0))) (contract_initializer_entry_65_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_0))))


(declare-fun |contract_initializer_after_init_66_C_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (contract_initializer_entry_65_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_66_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (contract_initializer_after_init_66_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_64_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_67_constructor_24_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_68__23_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(block_67_constructor_24_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (block_67_constructor_24_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_68__23_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_69_return_constructor_24_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (block_68__23_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_21_1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_1 expr_20_0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 a_2_1) (and (=> true true) (and (= expr_20_0 3) true)))))))) true) (block_69_return_constructor_24_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (block_69_return_constructor_24_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_17_constructor_24_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_70_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_71_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_71_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_72_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (contract_initializer_entry_71_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_72_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (contract_initializer_after_init_72_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_17_constructor_24_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_70_D_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (contract_initializer_after_init_72_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_17_constructor_24_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_70_D_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |contract_initializer_73_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_74_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_74_E_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_75_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (contract_initializer_entry_74_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_75_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (contract_initializer_after_init_75_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_73_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_76_constructor_10_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_77__9_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(block_76_constructor_10_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (block_76_constructor_10_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_77__9_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_78_return_constructor_10_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (block_77__9_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_78_return_constructor_10_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (block_78_return_constructor_10_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_16_constructor_10_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_79_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_80_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_80_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_81_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (contract_initializer_entry_80_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_81_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (contract_initializer_after_init_81_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_16_constructor_10_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_79_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (contract_initializer_after_init_81_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_16_constructor_10_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_79_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |implicit_constructor_entry_82_C_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_82_C_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (implicit_constructor_entry_82_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_79_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (summary_constructor_15_C_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (implicit_constructor_entry_82_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_73_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_79_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))) (> error_2 0)) (summary_constructor_15_C_28_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 a_2_0 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (implicit_constructor_entry_82_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_70_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_73_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_79_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))) (> error_3 0)) (summary_constructor_15_C_28_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 a_2_0 a_2_4))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (implicit_constructor_entry_82_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_64_C_28_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_70_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_73_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_79_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))))) (> error_4 0)) (summary_constructor_15_C_28_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_5 a_2_0 a_2_5))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (implicit_constructor_entry_82_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (= error_4 0) (and (contract_initializer_64_C_28_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_70_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_73_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_79_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))))))))) true) (summary_constructor_15_C_28_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_5 a_2_0 a_2_5))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int))
(=> (and (and (summary_constructor_15_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_13_C_28_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |block_83_constructor_38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_84__37_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(block_83_constructor_38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_83_constructor_38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_84__37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_85_return_constructor_38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_84__37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_35_1) (and (=> true (and (>= expr_35_1 0) (<= expr_35_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_35_1 expr_34_0) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 a_2_1) (and (=> true true) (and (= expr_34_0 4) true)))))))) true) (block_85_return_constructor_38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_85_return_constructor_38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_23_constructor_38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_86_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_87_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_87_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_88_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_entry_87_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_88_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_88_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_23_constructor_38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_86_B_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_88_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_23_constructor_38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_86_B_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |contract_initializer_89_C_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_90_C_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_90_C_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_91_C_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_entry_90_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_91_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_91_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_89_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_92_constructor_24_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_93__23_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(block_92_constructor_24_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_92_constructor_24_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_93__23_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_94_return_constructor_24_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_93__23_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_21_1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_1 expr_20_0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 a_2_1) (and (=> true true) (and (= expr_20_0 3) true)))))))) true) (block_94_return_constructor_24_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_94_return_constructor_24_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_22_constructor_24_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_95_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_96_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_96_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_97_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_entry_96_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_97_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_97_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_22_constructor_24_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_95_D_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_97_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_22_constructor_24_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_95_D_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |contract_initializer_98_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_99_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_99_E_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_100_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_entry_99_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_100_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_100_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_98_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_101_constructor_10_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_102__9_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(block_101_constructor_10_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_101_constructor_10_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_102__9_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_103_return_constructor_10_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_102__9_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_103_return_constructor_10_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_103_return_constructor_10_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_21_constructor_10_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_104_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_105_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_105_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_106_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_entry_105_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_106_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_106_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_21_constructor_10_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_104_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_106_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_21_constructor_10_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_104_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |implicit_constructor_entry_107_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) true) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_107_B_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_107_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_104_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (summary_constructor_20_B_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_107_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_98_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_104_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))) (> error_2 0)) (summary_constructor_20_B_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_107_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_95_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_98_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_104_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))) (> error_3 0)) (summary_constructor_20_B_39_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_4))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_107_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_89_C_28_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_95_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_98_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_104_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))))) (> error_4 0)) (summary_constructor_20_B_39_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_5 a_2_5))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_107_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_86_B_39_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 a_2_5 state_6 a_2_6) (and (= error_4 0) (and (contract_initializer_89_C_28_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_95_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_98_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_104_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))))))) (> error_5 0)) (summary_constructor_20_B_39_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_6 a_2_6))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_107_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_5 0) (and (contract_initializer_86_B_39_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 a_2_5 state_6 a_2_6) (and (= error_4 0) (and (contract_initializer_89_C_28_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_95_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_98_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_104_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))))))))))) true) (summary_constructor_20_B_39_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_6 a_2_6))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_1 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (summary_constructor_20_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_18_B_39_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |block_108_constructor_59_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_109__58_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(block_108_constructor_59_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_108_constructor_59_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_43_1 x_43_0))) true)) true) (block_109__58_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1))))


(declare-fun |block_110_return_constructor_59_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_111_constructor_59_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_109__58_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1) (and (= expr_49_1 (= expr_47_0 expr_48_0)) (and (=> true true) (and (= expr_48_0 4) (and (=> true (and (>= expr_47_0 0) (<= expr_47_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_47_0 a_2_1) (and (and (>= x_43_1 0) (<= x_43_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))) (and (not expr_49_1) (= error_1 1))) (block_111_constructor_59_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (block_111_constructor_59_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1) (summary_30_constructor_59_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1))))


(declare-fun |block_112_constructor_59_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_109__58_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1) (and (= expr_55_1 (= expr_53_0 expr_54_0)) (and (=> true true) (and (= expr_54_0 5) (and (=> true (and (>= expr_53_0 0) (<= expr_53_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_53_0 a_2_1) (and (= error_1 error_0) (and (= expr_49_1 (= expr_47_0 expr_48_0)) (and (=> true true) (and (= expr_48_0 4) (and (=> true (and (>= expr_47_0 0) (<= expr_47_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_47_0 a_2_1) (and (and (>= x_43_1 0) (<= x_43_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))))))) (and (not expr_55_1) (= error_2 2))) (block_112_constructor_59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (block_112_constructor_59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1) (summary_30_constructor_59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_109__58_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1) (and (= error_2 error_1) (and (= expr_55_1 (= expr_53_0 expr_54_0)) (and (=> true true) (and (= expr_54_0 5) (and (=> true (and (>= expr_53_0 0) (<= expr_53_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_53_0 a_2_1) (and (= error_1 error_0) (and (= expr_49_1 (= expr_47_0 expr_48_0)) (and (=> true true) (and (= expr_48_0 4) (and (=> true (and (>= expr_47_0 0) (<= expr_47_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_47_0 a_2_1) (and (and (>= x_43_1 0) (<= x_43_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))))) true) (block_110_return_constructor_59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_110_return_constructor_59_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1) true) true) (summary_30_constructor_59_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1))))


(declare-fun |contract_initializer_113_A_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_114_A_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_43_1 x_43_0))) (contract_initializer_entry_114_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1))))


(declare-fun |contract_initializer_after_init_115_A_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_entry_114_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1) true) true) (contract_initializer_after_init_115_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_115_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1) (and (summary_30_constructor_59_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_43_1 state_2 a_2_2 x_43_2) true)) (> error_1 0)) (contract_initializer_113_A_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_2 a_2_2 x_43_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_115_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_1) (and (= error_1 0) (and (summary_30_constructor_59_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_43_1 state_2 a_2_2 x_43_2) true))) true) (contract_initializer_113_A_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_2 a_2_2 x_43_2))))


(declare-fun |block_116_constructor_38_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_117__37_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(block_116_constructor_38_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_116_constructor_38_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_117__37_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_118_return_constructor_38_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_117__37_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_35_1) (and (=> true (and (>= expr_35_1 0) (<= expr_35_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_35_1 expr_34_0) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 a_2_1) (and (=> true true) (and (= expr_34_0 4) true)))))))) true) (block_118_return_constructor_38_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_118_return_constructor_38_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_29_constructor_38_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_119_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_120_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_120_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_121_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_entry_120_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_121_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_121_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_29_constructor_38_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_119_B_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_121_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_29_constructor_38_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_119_B_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |contract_initializer_122_C_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_123_C_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_123_C_28_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_124_C_28_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_entry_123_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_124_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_124_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_122_C_28_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_125_constructor_24_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_126__23_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(block_125_constructor_24_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_125_constructor_24_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_126__23_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_127_return_constructor_24_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_126__23_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_21_1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_1 expr_20_0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 a_2_1) (and (=> true true) (and (= expr_20_0 3) true)))))))) true) (block_127_return_constructor_24_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_127_return_constructor_24_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_28_constructor_24_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_128_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_129_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_129_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_130_D_25_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_entry_129_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_130_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_130_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_28_constructor_24_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_128_D_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_130_D_25_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_28_constructor_24_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_128_D_25_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |contract_initializer_131_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_132_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_132_E_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_133_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_entry_132_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_133_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_133_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_131_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_134_constructor_10_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_135__9_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(block_134_constructor_10_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_134_constructor_10_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_135__9_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_136_return_constructor_10_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_135__9_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_136_return_constructor_10_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (block_136_return_constructor_10_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_27_constructor_10_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_137_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_138_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_138_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_139_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_entry_138_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_139_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_139_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_27_constructor_10_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_137_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (contract_initializer_after_init_139_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_27_constructor_10_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_137_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |implicit_constructor_entry_140_A_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= x_43_2 x_43_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_140_A_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_2 a_2_2 x_43_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_140_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_2) (and (contract_initializer_137_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (summary_constructor_26_A_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_2 a_2_2 x_43_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_140_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_2) (and (contract_initializer_131_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_137_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))) (> error_2 0)) (summary_constructor_26_A_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_3 a_2_3 x_43_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_140_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_2) (and (contract_initializer_128_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_131_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_137_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))) (> error_3 0)) (summary_constructor_26_A_60_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_4 a_2_4 x_43_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_140_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_2) (and (contract_initializer_122_C_28_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_128_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_131_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_137_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))))) (> error_4 0)) (summary_constructor_26_A_60_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_5 a_2_5 x_43_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_140_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_2) (and (contract_initializer_119_B_39_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 a_2_5 state_6 a_2_6) (and (= error_4 0) (and (contract_initializer_122_C_28_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_128_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_131_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_137_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))))))) (> error_5 0)) (summary_constructor_26_A_60_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_6 a_2_6 x_43_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_140_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_2) (and (contract_initializer_113_A_60_0 error_6 this_0 abi_0 crypto_0 tx_0 state_6 a_2_6 x_43_2 state_7 a_2_7 x_43_3) (and (= error_5 0) (and (contract_initializer_119_B_39_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 a_2_5 state_6 a_2_6) (and (= error_4 0) (and (contract_initializer_122_C_28_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_128_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_131_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_137_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))))))))) (> error_6 0)) (summary_constructor_26_A_60_0 error_6 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_7 a_2_7 x_43_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (implicit_constructor_entry_140_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_2) (and (= error_6 0) (and (contract_initializer_113_A_60_0 error_6 this_0 abi_0 crypto_0 tx_0 state_6 a_2_6 x_43_2 state_7 a_2_7 x_43_3) (and (= error_5 0) (and (contract_initializer_119_B_39_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 a_2_5 state_6 a_2_6) (and (= error_4 0) (and (contract_initializer_122_C_28_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_128_D_25_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_131_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_137_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))))))))))))) true) (summary_constructor_26_A_60_0 error_6 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_7 a_2_7 x_43_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (summary_constructor_26_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_24_A_60_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> (and (and (summary_constructor_26_A_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_43_0 state_1 a_2_1 x_43_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_19_0 Int) (expr_20_0 Int) (expr_21_1 Int) (expr_33_0 Int) (expr_34_0 Int) (expr_35_1 Int) (expr_47_0 Int) (expr_48_0 Int) (expr_49_1 Bool) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_43_0 Int) (x_43_1 Int) (x_43_10 Int) (x_43_11 Int) (x_43_2 Int) (x_43_3 Int) (x_43_4 Int) (x_43_5 Int) (x_43_6 Int) (x_43_7 Int) (x_43_8 Int) (x_43_9 Int))
(=> error_target_3_0 false)))
(check-sat)