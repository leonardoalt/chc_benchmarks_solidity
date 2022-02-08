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
(declare-fun |interface_8_D_17_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_9_D_17_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_10_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_9_D_17_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_11_constructor_10_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_12_C_20_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_13_C_20_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_14_C_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_13_C_20_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_15_constructor_10_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_16_B_23_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_17_B_23_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_18_B_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_17_B_23_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_19_constructor_10_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_20_A_44_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_21_A_44_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_22_A_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_21_A_44_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_23_constructor_10_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_24_constructor_43_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_25_constructor_10_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_26__9_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int))
(block_25_constructor_10_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int))
(=> (and (and (block_25_constructor_10_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_26__9_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_27_return_constructor_10_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int))
(=> (and (and (block_26__9_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_27_return_constructor_10_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int))
(=> (and (and (block_27_return_constructor_10_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_3_constructor_10_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_28_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_29_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_29_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_30_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int))
(=> (and (and (contract_initializer_entry_29_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_30_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int))
(=> (and (and (contract_initializer_after_init_30_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_3_constructor_10_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_28_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int))
(=> (and (and (contract_initializer_after_init_30_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_3_constructor_10_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_28_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |implicit_constructor_entry_31_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) true) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_31_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int))
(=> (and (and (implicit_constructor_entry_31_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_28_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (summary_constructor_2_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int))
(=> (and (and (implicit_constructor_entry_31_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (contract_initializer_28_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (summary_constructor_2_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int))
(=> (and (and (summary_constructor_2_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_F_11_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |contract_initializer_32_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_33_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_0 a_2_0))) (contract_initializer_entry_33_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_0))))


(declare-fun |contract_initializer_after_init_34_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (contract_initializer_entry_33_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_34_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (contract_initializer_after_init_34_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_32_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_35_constructor_10_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_36__9_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(block_35_constructor_10_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (block_35_constructor_10_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_36__9_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_37_return_constructor_10_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (block_36__9_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_37_return_constructor_10_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (block_37_return_constructor_10_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_7_constructor_10_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_38_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_39_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_39_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_40_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (contract_initializer_entry_39_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_40_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (contract_initializer_after_init_40_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_7_constructor_10_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_38_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (contract_initializer_after_init_40_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_7_constructor_10_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_38_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |implicit_constructor_entry_41_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_41_E_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (implicit_constructor_entry_41_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_38_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (summary_constructor_6_E_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (implicit_constructor_entry_41_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_32_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_38_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))) (> error_2 0)) (summary_constructor_6_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 a_2_0 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (implicit_constructor_entry_41_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (= error_2 0) (and (contract_initializer_32_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_38_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))))) true) (summary_constructor_6_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 a_2_0 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int))
(=> (and (and (summary_constructor_6_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_4_E_14_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |contract_initializer_42_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_43_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_0 a_2_0))) (contract_initializer_entry_43_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_0))))


(declare-fun |contract_initializer_after_init_44_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (contract_initializer_entry_43_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_44_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (contract_initializer_after_init_44_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_42_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_45_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_46_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (contract_initializer_entry_46_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_after_init_47_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (contract_initializer_entry_46_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_47_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (contract_initializer_after_init_47_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_45_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_48_constructor_10_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_49__9_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(block_48_constructor_10_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (block_48_constructor_10_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_49__9_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_50_return_constructor_10_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (block_49__9_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_50_return_constructor_10_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (block_50_return_constructor_10_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_11_constructor_10_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_51_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_52_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_52_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_53_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (contract_initializer_entry_52_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_53_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (contract_initializer_after_init_53_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_11_constructor_10_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_51_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (contract_initializer_after_init_53_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_11_constructor_10_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_51_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |implicit_constructor_entry_54_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_54_D_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (implicit_constructor_entry_54_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_51_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (summary_constructor_10_D_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (implicit_constructor_entry_54_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_45_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_51_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))) (> error_2 0)) (summary_constructor_10_D_17_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 a_2_0 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (implicit_constructor_entry_54_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_42_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_45_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_51_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))) (> error_3 0)) (summary_constructor_10_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 a_2_0 a_2_4))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (implicit_constructor_entry_54_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (= error_3 0) (and (contract_initializer_42_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_45_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_51_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))))))) true) (summary_constructor_10_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 a_2_0 a_2_4))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int))
(=> (and (and (summary_constructor_10_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_8_D_17_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |contract_initializer_55_C_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_56_C_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_0 a_2_0))) (contract_initializer_entry_56_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_0))))


(declare-fun |contract_initializer_after_init_57_C_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (contract_initializer_entry_56_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_57_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (contract_initializer_after_init_57_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_55_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_58_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_59_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (contract_initializer_entry_59_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_after_init_60_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (contract_initializer_entry_59_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_60_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (contract_initializer_after_init_60_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_58_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_61_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_62_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (contract_initializer_entry_62_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_after_init_63_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (contract_initializer_entry_62_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_63_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (contract_initializer_after_init_63_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_61_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_64_constructor_10_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_65__9_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(block_64_constructor_10_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (block_64_constructor_10_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_65__9_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_66_return_constructor_10_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (block_65__9_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_66_return_constructor_10_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (block_66_return_constructor_10_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_15_constructor_10_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_67_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_68_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_68_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_69_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (contract_initializer_entry_68_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_69_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (contract_initializer_after_init_69_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_15_constructor_10_20_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_67_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (contract_initializer_after_init_69_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_15_constructor_10_20_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_67_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |implicit_constructor_entry_70_C_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_70_C_20_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (implicit_constructor_entry_70_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_67_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (summary_constructor_14_C_20_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (implicit_constructor_entry_70_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_61_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_67_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))) (> error_2 0)) (summary_constructor_14_C_20_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 a_2_0 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (implicit_constructor_entry_70_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_58_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_61_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_67_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))) (> error_3 0)) (summary_constructor_14_C_20_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 a_2_0 a_2_4))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (implicit_constructor_entry_70_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_55_C_20_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_58_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_61_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_67_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))))) (> error_4 0)) (summary_constructor_14_C_20_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_5 a_2_0 a_2_5))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (implicit_constructor_entry_70_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (= error_4 0) (and (contract_initializer_55_C_20_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_58_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_61_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_67_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))))))))) true) (summary_constructor_14_C_20_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_5 a_2_0 a_2_5))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int))
(=> (and (and (summary_constructor_14_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_12_C_20_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |contract_initializer_71_B_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_72_B_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_0 a_2_0))) (contract_initializer_entry_72_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_0))))


(declare-fun |contract_initializer_after_init_73_B_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_entry_72_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_73_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_73_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_71_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_74_C_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_75_C_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (contract_initializer_entry_75_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_after_init_76_C_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_entry_75_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_76_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_76_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_74_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_77_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_78_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (contract_initializer_entry_78_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_after_init_79_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_entry_78_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_79_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_79_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_77_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_80_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_81_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (contract_initializer_entry_81_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_after_init_82_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_entry_81_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_82_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_82_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_80_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_83_constructor_10_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_84__9_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(block_83_constructor_10_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (block_83_constructor_10_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_84__9_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_85_return_constructor_10_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (block_84__9_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_85_return_constructor_10_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (block_85_return_constructor_10_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_19_constructor_10_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_86_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_87_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_87_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_88_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_entry_87_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_88_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_88_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_19_constructor_10_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_86_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_88_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_19_constructor_10_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_86_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |implicit_constructor_entry_89_B_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_89_B_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_89_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_86_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (summary_constructor_18_B_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_89_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_80_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_86_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))) (> error_2 0)) (summary_constructor_18_B_23_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 a_2_0 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_89_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_77_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_80_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_86_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))) (> error_3 0)) (summary_constructor_18_B_23_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 a_2_0 a_2_4))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_89_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_74_C_20_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_77_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_80_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_86_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))))) (> error_4 0)) (summary_constructor_18_B_23_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_5 a_2_0 a_2_5))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_89_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_71_B_23_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 state_6 a_2_5 a_2_6) (and (= error_4 0) (and (contract_initializer_74_C_20_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_77_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_80_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_86_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))))))) (> error_5 0)) (summary_constructor_18_B_23_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 state_6 a_2_0 a_2_6))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_89_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (= error_5 0) (and (contract_initializer_71_B_23_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 state_6 a_2_5 a_2_6) (and (= error_4 0) (and (contract_initializer_74_C_20_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_77_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_80_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_86_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))))))))))) true) (summary_constructor_18_B_23_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 state_6 a_2_0 a_2_6))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_1 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (summary_constructor_18_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_16_B_23_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |block_90_constructor_43_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_91__42_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(block_90_constructor_43_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (block_90_constructor_43_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_27_1 x_27_0))) true)) true) (block_91__42_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1))))


(declare-fun |block_92_return_constructor_43_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_93_constructor_43_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (block_91__42_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1) (and (= expr_33_1 (= expr_31_0 expr_32_0)) (and (=> true true) (and (= expr_32_0 2) (and (=> true (and (>= expr_31_0 0) (<= expr_31_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_31_0 a_2_1) (and (and (>= x_27_1 0) (<= x_27_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))) (and (not expr_33_1) (= error_1 1))) (block_93_constructor_43_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (block_93_constructor_43_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1) (summary_24_constructor_43_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1))))


(declare-fun |block_94_constructor_43_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (block_91__42_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1) (and (= expr_39_1 (= expr_37_0 expr_38_0)) (and (=> true true) (and (= expr_38_0 3) (and (=> true (and (>= expr_37_0 0) (<= expr_37_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_37_0 a_2_1) (and (= error_1 error_0) (and (= expr_33_1 (= expr_31_0 expr_32_0)) (and (=> true true) (and (= expr_32_0 2) (and (=> true (and (>= expr_31_0 0) (<= expr_31_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_31_0 a_2_1) (and (and (>= x_27_1 0) (<= x_27_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))))))) (and (not expr_39_1) (= error_2 2))) (block_94_constructor_43_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (block_94_constructor_43_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1) (summary_24_constructor_43_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (block_91__42_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1) (and (= error_2 error_1) (and (= expr_39_1 (= expr_37_0 expr_38_0)) (and (=> true true) (and (= expr_38_0 3) (and (=> true (and (>= expr_37_0 0) (<= expr_37_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_37_0 a_2_1) (and (= error_1 error_0) (and (= expr_33_1 (= expr_31_0 expr_32_0)) (and (=> true true) (and (= expr_32_0 2) (and (=> true (and (>= expr_31_0 0) (<= expr_31_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_31_0 a_2_1) (and (and (>= x_27_1 0) (<= x_27_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))))) true) (block_92_return_constructor_43_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (block_92_return_constructor_43_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1) true) true) (summary_24_constructor_43_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1))))


(declare-fun |contract_initializer_95_A_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_96_A_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_27_1 x_27_0))) (contract_initializer_entry_96_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1))))


(declare-fun |contract_initializer_after_init_97_A_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_entry_96_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1) true) true) (contract_initializer_after_init_97_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_97_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1) (and (summary_24_constructor_43_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_27_1 state_2 a_2_2 x_27_2) true)) (> error_1 0)) (contract_initializer_95_A_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_2 a_2_2 x_27_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_97_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_1) (and (= error_1 0) (and (summary_24_constructor_43_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_27_1 state_2 a_2_2 x_27_2) true))) true) (contract_initializer_95_A_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_2 a_2_2 x_27_2))))


(declare-fun |contract_initializer_98_B_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_99_B_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_99_B_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_100_B_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_entry_99_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_100_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_100_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_98_B_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_101_C_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_102_C_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (contract_initializer_entry_102_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_after_init_103_C_20_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_entry_102_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_103_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_103_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_101_C_20_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_104_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_105_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (contract_initializer_entry_105_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_after_init_106_D_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_entry_105_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_106_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_106_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_104_D_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_107_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_108_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (contract_initializer_entry_108_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |contract_initializer_after_init_109_E_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_entry_108_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_109_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_109_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_107_E_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_110_constructor_10_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_111__9_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(block_110_constructor_10_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (block_110_constructor_10_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_111__9_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_112_return_constructor_10_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (block_111__9_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 2) true)))))))) true) (block_112_return_constructor_10_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (block_112_return_constructor_10_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_23_constructor_10_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_113_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_114_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_114_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_115_F_11_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_entry_114_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_115_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_115_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_23_constructor_10_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_113_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (contract_initializer_after_init_115_F_11_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_23_constructor_10_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_113_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |implicit_constructor_entry_116_A_44_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= x_27_2 x_27_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_116_A_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_2 a_2_2 x_27_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_116_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_2) (and (contract_initializer_113_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (summary_constructor_22_A_44_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_2 a_2_2 x_27_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_116_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_2) (and (contract_initializer_107_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_113_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))) (> error_2 0)) (summary_constructor_22_A_44_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_3 a_2_3 x_27_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_116_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_2) (and (contract_initializer_104_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_107_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_113_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))) (> error_3 0)) (summary_constructor_22_A_44_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_4 a_2_4 x_27_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_116_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_2) (and (contract_initializer_101_C_20_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_104_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_107_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_113_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))))) (> error_4 0)) (summary_constructor_22_A_44_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_5 a_2_5 x_27_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_116_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_2) (and (contract_initializer_98_B_23_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 state_6 a_2_5 a_2_6) (and (= error_4 0) (and (contract_initializer_101_C_20_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_104_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_107_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_113_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))))))) (> error_5 0)) (summary_constructor_22_A_44_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_6 a_2_6 x_27_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_116_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_2) (and (contract_initializer_95_A_44_0 error_6 this_0 abi_0 crypto_0 tx_0 state_6 a_2_6 x_27_2 state_7 a_2_7 x_27_3) (and (= error_5 0) (and (contract_initializer_98_B_23_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 state_6 a_2_5 a_2_6) (and (= error_4 0) (and (contract_initializer_101_C_20_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_104_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_107_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_113_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)))))))))))) (> error_6 0)) (summary_constructor_22_A_44_0 error_6 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_7 a_2_7 x_27_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (implicit_constructor_entry_116_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_2) (and (= error_6 0) (and (contract_initializer_95_A_44_0 error_6 this_0 abi_0 crypto_0 tx_0 state_6 a_2_6 x_27_2 state_7 a_2_7 x_27_3) (and (= error_5 0) (and (contract_initializer_98_B_23_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 state_6 a_2_5 a_2_6) (and (= error_4 0) (and (contract_initializer_101_C_20_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_104_D_17_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 a_2_3 a_2_4) (and (= error_2 0) (and (contract_initializer_107_E_14_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_113_F_11_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))))))))))))) true) (summary_constructor_22_A_44_0 error_6 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_7 a_2_7 x_27_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (summary_constructor_22_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_20_A_44_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (summary_constructor_22_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_3_0)))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> (and (and (summary_constructor_22_A_44_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_27_0 state_1 a_2_1 x_27_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 2))) error_target_4_0)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_31_0 Int) (expr_32_0 Int) (expr_33_1 Bool) (expr_37_0 Int) (expr_38_0 Int) (expr_39_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_27_0 Int) (x_27_1 Int) (x_27_10 Int) (x_27_11 Int) (x_27_2 Int) (x_27_3 Int) (x_27_4 Int) (x_27_5 Int) (x_27_6 Int) (x_27_7 Int) (x_27_8 Int) (x_27_9 Int))
(=> error_target_4_0 false)))
(check-sat)