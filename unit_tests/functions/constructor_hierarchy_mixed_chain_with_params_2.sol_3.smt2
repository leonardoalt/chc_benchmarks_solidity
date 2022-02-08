(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_F_13_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_F_13_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_F_13_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_3_constructor_12_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |interface_4_E_16_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_5_E_16_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_6_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_5_E_16_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_7_constructor_12_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |interface_8_D_27_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_9_D_27_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_10_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_9_D_27_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_11_constructor_12_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_12_constructor_26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_13_C_30_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_14_C_30_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_15_C_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_14_C_30_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_16_constructor_12_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_17_constructor_26_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_18_B_52_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_19_B_52_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_20_B_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_19_B_52_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_21_constructor_12_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_22_constructor_26_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_23_constructor_51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_24_A_55_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_25_A_55_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_26_A_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_25_A_55_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_27_constructor_12_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_28_constructor_26_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_29_constructor_51_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_30_constructor_12_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_31__11_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(block_30_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_30_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_31__11_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_32_return_constructor_12_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_31__11_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_32_return_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_32_return_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_3_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_33_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_34_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_34_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_35_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (contract_initializer_entry_34_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_35_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_35_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_3_constructor_12_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_33_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_35_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_3_constructor_12_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_33_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_36_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= x_4_2 x_4_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_36_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (implicit_constructor_entry_36_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_2) (and (contract_initializer_33_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)) (> error_1 0)) (summary_constructor_2_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (implicit_constructor_entry_36_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_2) (and (= error_1 0) (and (contract_initializer_33_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true))) true) (summary_constructor_2_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (summary_constructor_2_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_F_13_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |contract_initializer_37_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_38_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_0 a_2_0))) (contract_initializer_entry_38_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_0))))


(declare-fun |contract_initializer_after_init_39_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_38_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_39_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_39_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_37_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_40_constructor_12_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_41__11_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_40_constructor_12_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_40_constructor_12_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_41__11_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_42_return_constructor_12_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_41__11_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_42_return_constructor_12_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_42_return_constructor_12_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_7_constructor_12_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_43_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_44_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_44_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_45_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_44_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_45_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_45_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_7_constructor_12_16_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_43_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_45_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_7_constructor_12_16_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_43_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_46_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_46_E_16_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_46_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_43_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)) (> error_1 0)) (summary_constructor_6_E_16_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_46_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_37_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_43_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)))) (> error_2 0)) (summary_constructor_6_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 a_2_0 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_46_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (= error_2 0) (and (contract_initializer_37_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_43_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true))))) true) (summary_constructor_6_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 a_2_0 a_2_3))))


(declare-fun |block_47_constructor_26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_48__25_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_47_constructor_26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_47_constructor_26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_48__25_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_49_return_constructor_26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_48__25_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_23_1) (and (=> true (and (>= expr_23_1 0) (<= expr_23_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_1 expr_22_0) (and (=> true (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 a_2_1) (and (=> true true) (and (= expr_22_0 3) true)))))))) true) (block_49_return_constructor_26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_49_return_constructor_26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_12_constructor_26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_50_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_51_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_51_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_52_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_51_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_52_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_52_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_12_constructor_26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_50_D_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_52_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_12_constructor_26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_50_D_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |contract_initializer_53_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_54_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_54_E_16_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_55_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_54_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_55_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_55_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_53_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_56_constructor_12_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_57__11_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_56_constructor_12_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_56_constructor_12_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_57__11_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_58_return_constructor_12_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_57__11_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_58_return_constructor_12_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_58_return_constructor_12_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_11_constructor_12_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_59_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_60_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_60_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_61_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_60_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_61_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_61_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_11_constructor_12_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_59_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_61_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_11_constructor_12_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_59_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_62_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) true) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_62_D_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_62_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_59_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)) (> error_1 0)) (summary_constructor_10_D_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_62_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_53_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_59_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)))) (> error_2 0)) (summary_constructor_10_D_27_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_62_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_50_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_53_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_59_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)))))) (> error_3 0)) (summary_constructor_10_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_4))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_62_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_3 0) (and (contract_initializer_50_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_53_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_59_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true))))))) true) (summary_constructor_10_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_4))))


(declare-fun |contract_initializer_63_C_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_64_C_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_0 a_2_0))) (contract_initializer_entry_64_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_0))))


(declare-fun |contract_initializer_after_init_65_C_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_64_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_65_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_65_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_63_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_66_constructor_26_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_67__25_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_66_constructor_26_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_66_constructor_26_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_67__25_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_68_return_constructor_26_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_67__25_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_23_1) (and (=> true (and (>= expr_23_1 0) (<= expr_23_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_1 expr_22_0) (and (=> true (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 a_2_1) (and (=> true true) (and (= expr_22_0 3) true)))))))) true) (block_68_return_constructor_26_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_68_return_constructor_26_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_17_constructor_26_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_69_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_70_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_70_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_71_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_70_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_71_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_71_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_17_constructor_26_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_69_D_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_71_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_17_constructor_26_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_69_D_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |contract_initializer_72_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_73_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_73_E_16_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_74_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_73_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_74_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_74_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_72_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_75_constructor_12_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_76__11_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_75_constructor_12_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_75_constructor_12_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_76__11_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_77_return_constructor_12_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_76__11_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_77_return_constructor_12_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_77_return_constructor_12_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_16_constructor_12_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_78_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_79_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_79_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_80_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_79_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_80_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_80_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_16_constructor_12_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_78_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_80_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_16_constructor_12_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_78_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_81_C_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_81_C_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_81_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_78_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)) (> error_1 0)) (summary_constructor_15_C_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_81_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_72_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_78_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)))) (> error_2 0)) (summary_constructor_15_C_30_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 a_2_0 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_81_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_69_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_72_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_78_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)))))) (> error_3 0)) (summary_constructor_15_C_30_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 a_2_0 a_2_4))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_81_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_63_C_30_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_69_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_72_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_78_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)))))))) (> error_4 0)) (summary_constructor_15_C_30_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_5 a_2_0 a_2_5))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_81_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (= error_4 0) (and (contract_initializer_63_C_30_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_69_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_72_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_78_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true))))))))) true) (summary_constructor_15_C_30_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_5 a_2_0 a_2_5))))


(declare-fun |block_82_constructor_51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_83__50_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_82_constructor_51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_82_constructor_51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_83__50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_84_return_constructor_51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_85_constructor_51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_83__50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= expr_41_1 (= expr_39_0 expr_40_0)) (and (=> true true) (and (= expr_40_0 3) (and (=> true (and (>= expr_39_0 0) (<= expr_39_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_39_0 a_2_1) true)))))) (and (not expr_41_1) (= error_1 1))) (block_85_constructor_51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (block_85_constructor_51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (summary_23_constructor_51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_86_constructor_51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_83__50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= expr_47_1 (= expr_45_0 expr_46_0)) (and (=> true true) (and (= expr_46_0 2) (and (=> true (and (>= expr_45_0 0) (<= expr_45_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_45_0 a_2_1) (and (= error_1 error_0) (and (= expr_41_1 (= expr_39_0 expr_40_0)) (and (=> true true) (and (= expr_40_0 3) (and (=> true (and (>= expr_39_0 0) (<= expr_39_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_39_0 a_2_1) true)))))))))))) (and (not expr_47_1) (= error_2 2))) (block_86_constructor_51_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (block_86_constructor_51_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (summary_23_constructor_51_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_83__50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_2 error_1) (and (= expr_47_1 (= expr_45_0 expr_46_0)) (and (=> true true) (and (= expr_46_0 2) (and (=> true (and (>= expr_45_0 0) (<= expr_45_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_45_0 a_2_1) (and (= error_1 error_0) (and (= expr_41_1 (= expr_39_0 expr_40_0)) (and (=> true true) (and (= expr_40_0 3) (and (=> true (and (>= expr_39_0 0) (<= expr_39_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_39_0 a_2_1) true))))))))))))) true) (block_84_return_constructor_51_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_84_return_constructor_51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_23_constructor_51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_87_B_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_88_B_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_88_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_89_B_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_88_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_89_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_89_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_23_constructor_51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_87_B_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_89_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_23_constructor_51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_87_B_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |contract_initializer_90_C_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_91_C_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_91_C_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_92_C_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_91_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_92_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_92_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_90_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_93_constructor_26_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_94__25_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_93_constructor_26_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_93_constructor_26_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_94__25_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_95_return_constructor_26_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_94__25_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_23_1) (and (=> true (and (>= expr_23_1 0) (<= expr_23_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_1 expr_22_0) (and (=> true (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 a_2_1) (and (=> true true) (and (= expr_22_0 3) true)))))))) true) (block_95_return_constructor_26_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_95_return_constructor_26_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_22_constructor_26_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_96_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_97_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_97_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_98_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_97_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_98_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_98_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_22_constructor_26_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_96_D_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_98_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_22_constructor_26_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_96_D_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |contract_initializer_99_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_100_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_100_E_16_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_101_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_100_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_101_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_101_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_99_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_102_constructor_12_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_103__11_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_102_constructor_12_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_102_constructor_12_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_103__11_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_104_return_constructor_12_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_103__11_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_104_return_constructor_12_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_104_return_constructor_12_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_21_constructor_12_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_105_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_106_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_106_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_107_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_106_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_107_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_107_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_21_constructor_12_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_105_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_107_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_21_constructor_12_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_105_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_108_B_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) true) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_108_B_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_108_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_105_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true))))) (> error_1 0)) (summary_constructor_20_B_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_108_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_99_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_105_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true))))))) (> error_2 0)) (summary_constructor_20_B_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_108_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_96_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_99_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_105_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true))))))))) (> error_3 0)) (summary_constructor_20_B_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_4 a_2_4))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_108_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_90_C_30_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_96_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_99_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_105_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true))))))))))) (> error_4 0)) (summary_constructor_20_B_52_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_5 a_2_5))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_108_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_87_B_52_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 a_2_5 state_6 a_2_6) (and (= error_4 0) (and (contract_initializer_90_C_30_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_96_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_99_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_105_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true))))))))))))) (> error_5 0)) (summary_constructor_20_B_52_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_6 a_2_6))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_108_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_5 0) (and (contract_initializer_87_B_52_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 a_2_5 state_6 a_2_6) (and (= error_4 0) (and (contract_initializer_90_C_30_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_96_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_99_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_105_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true)))))))))))))) true) (summary_constructor_20_B_52_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_6 a_2_6))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_20_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_18_B_52_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |contract_initializer_109_A_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_110_A_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_0 a_2_0))) (contract_initializer_entry_110_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_0))))


(declare-fun |contract_initializer_after_init_111_A_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_110_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_111_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_111_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_109_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_112_constructor_51_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_113__50_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_112_constructor_51_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_112_constructor_51_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_113__50_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_114_return_constructor_51_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_115_constructor_51_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_113__50_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= expr_41_1 (= expr_39_0 expr_40_0)) (and (=> true true) (and (= expr_40_0 3) (and (=> true (and (>= expr_39_0 0) (<= expr_39_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_39_0 a_2_1) true)))))) (and (not expr_41_1) (= error_1 3))) (block_115_constructor_51_55_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (block_115_constructor_51_55_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (summary_29_constructor_51_55_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_116_constructor_51_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_113__50_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= expr_47_1 (= expr_45_0 expr_46_0)) (and (=> true true) (and (= expr_46_0 2) (and (=> true (and (>= expr_45_0 0) (<= expr_45_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_45_0 a_2_1) (and (= error_1 error_0) (and (= expr_41_1 (= expr_39_0 expr_40_0)) (and (=> true true) (and (= expr_40_0 3) (and (=> true (and (>= expr_39_0 0) (<= expr_39_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_39_0 a_2_1) true)))))))))))) (and (not expr_47_1) (= error_2 4))) (block_116_constructor_51_55_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (block_116_constructor_51_55_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (summary_29_constructor_51_55_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_113__50_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_2 error_1) (and (= expr_47_1 (= expr_45_0 expr_46_0)) (and (=> true true) (and (= expr_46_0 2) (and (=> true (and (>= expr_45_0 0) (<= expr_45_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_45_0 a_2_1) (and (= error_1 error_0) (and (= expr_41_1 (= expr_39_0 expr_40_0)) (and (=> true true) (and (= expr_40_0 3) (and (=> true (and (>= expr_39_0 0) (<= expr_39_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_39_0 a_2_1) true))))))))))))) true) (block_114_return_constructor_51_55_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_114_return_constructor_51_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_29_constructor_51_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_117_B_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_118_B_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_118_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_119_B_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_118_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_119_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_119_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_29_constructor_51_55_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_117_B_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_119_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_29_constructor_51_55_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_117_B_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |contract_initializer_120_C_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_121_C_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_121_C_30_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_122_C_30_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_121_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_122_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_122_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_120_C_30_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_123_constructor_26_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_124__25_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_123_constructor_26_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_123_constructor_26_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_124__25_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_125_return_constructor_26_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_124__25_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= a_2_2 expr_23_1) (and (=> true (and (>= expr_23_1 0) (<= expr_23_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_1 expr_22_0) (and (=> true (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 a_2_1) (and (=> true true) (and (= expr_22_0 3) true)))))))) true) (block_125_return_constructor_26_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_125_return_constructor_26_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_28_constructor_26_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_126_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_127_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_127_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_128_D_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_127_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_128_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_128_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_28_constructor_26_55_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_126_D_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_128_D_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_28_constructor_26_55_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_126_D_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |contract_initializer_129_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_130_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (contract_initializer_entry_130_E_16_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(declare-fun |contract_initializer_after_init_131_E_16_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_130_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_after_init_131_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_131_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) true) (contract_initializer_129_E_16_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1))))


(declare-fun |block_132_constructor_12_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_133__11_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_132_constructor_12_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_132_constructor_12_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_133__11_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_134_return_constructor_12_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_133__11_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_134_return_constructor_12_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_134_return_constructor_12_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_27_constructor_12_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_135_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_136_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_136_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_137_F_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_136_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_137_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_137_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_27_constructor_12_55_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_135_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_137_F_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_27_constructor_12_55_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_135_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_138_A_55_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_138_A_55_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_138_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_135_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true))))) (> error_1 0)) (summary_constructor_26_A_55_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 a_2_0 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_138_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_129_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_135_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true))))))) (> error_2 0)) (summary_constructor_26_A_55_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 a_2_0 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_138_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_126_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_129_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_135_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true))))))))) (> error_3 0)) (summary_constructor_26_A_55_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 a_2_0 a_2_4))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_138_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_120_C_30_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_126_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_129_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_135_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true))))))))))) (> error_4 0)) (summary_constructor_26_A_55_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_5 a_2_0 a_2_5))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_138_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_117_B_52_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 a_2_5 state_6 a_2_6) (and (= error_4 0) (and (contract_initializer_120_C_30_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_126_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_129_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_135_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true))))))))))))) (> error_5 0)) (summary_constructor_26_A_55_0 error_5 this_0 abi_0 crypto_0 tx_0 state_0 state_6 a_2_0 a_2_6))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_138_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (contract_initializer_109_A_55_0 error_6 this_0 abi_0 crypto_0 tx_0 state_6 state_7 a_2_6 a_2_7) (and (= error_5 0) (and (contract_initializer_117_B_52_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 a_2_5 state_6 a_2_6) (and (= error_4 0) (and (contract_initializer_120_C_30_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_126_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_129_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_135_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true))))))))))))))) (> error_6 0)) (summary_constructor_26_A_55_0 error_6 this_0 abi_0 crypto_0 tx_0 state_0 state_7 a_2_0 a_2_7))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_138_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) (and (= error_6 0) (and (contract_initializer_109_A_55_0 error_6 this_0 abi_0 crypto_0 tx_0 state_6 state_7 a_2_6 a_2_7) (and (= error_5 0) (and (contract_initializer_117_B_52_0 error_5 this_0 abi_0 crypto_0 tx_0 state_5 a_2_5 state_6 a_2_6) (and (= error_4 0) (and (contract_initializer_120_C_30_0 error_4 this_0 abi_0 crypto_0 tx_0 state_4 state_5 a_2_4 a_2_5) (and (= error_3 0) (and (contract_initializer_126_D_27_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 state_4 a_2_4) (and (= error_2 0) (and (contract_initializer_129_E_16_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 a_2_2 a_2_3) (and (= error_1 0) (and (contract_initializer_135_F_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_35_0) (and (=> true true) (and (= expr_35_0 1) true)))))))))))))))) true) (summary_constructor_26_A_55_0 error_6 this_0 abi_0 crypto_0 tx_0 state_0 state_7 a_2_0 a_2_7))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_26_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_24_A_55_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_20_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_5_0)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_26_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_5_0)))


(declare-fun |error_target_6_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_20_B_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 2))) error_target_6_0)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_26_A_55_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 a_2_0 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 2))) error_target_6_0)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (a_2_5 Int) (a_2_6 Int) (a_2_7 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (error_5 Int) (error_6 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_35_0 Int) (expr_39_0 Int) (expr_40_0 Int) (expr_41_1 Bool) (expr_45_0 Int) (expr_46_0 Int) (expr_47_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (state_5 |state_type|) (state_6 |state_type|) (state_7 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> error_target_6_0 false)))
(check-sat)