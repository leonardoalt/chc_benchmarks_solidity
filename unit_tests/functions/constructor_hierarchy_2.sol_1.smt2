(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_13_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_13_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_13_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_3_constructor_12_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |interface_4_A_29_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_5_A_29_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_6_A_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_5_A_29_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_7_constructor_12_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_8_constructor_28_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_9_B_45_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_10_B_45_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_11_B_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_10_B_45_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_12_constructor_12_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_13_constructor_44_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_14_J_61_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_15_J_61_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_16_J_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_15_J_61_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_17_constructor_12_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_18_constructor_60_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_19_constructor_12_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_20__11_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(block_19_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_19_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_20__11_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_21_return_constructor_12_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_20__11_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_21_return_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_21_return_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_3_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_22_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_23_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_23_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_24_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (contract_initializer_entry_23_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_24_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_24_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_3_constructor_12_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_22_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_24_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_3_constructor_12_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_22_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_25_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= x_4_2 x_4_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_25_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (implicit_constructor_entry_25_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_2) (and (contract_initializer_22_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)) (> error_1 0)) (summary_constructor_2_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (implicit_constructor_entry_25_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_2) (and (= error_1 0) (and (contract_initializer_22_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true))) true) (summary_constructor_2_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (summary_constructor_2_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_13_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |block_26_constructor_28_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_27__27_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_26_constructor_28_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_26_constructor_28_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_27__27_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_28_return_constructor_28_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_29_constructor_28_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_27__27_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= expr_24_1 (= expr_22_0 expr_23_0)) (and (=> true true) (and (= expr_23_0 2) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 a_2_1) true)))))) (and (not expr_24_1) (= error_1 1))) (block_29_constructor_28_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (block_29_constructor_28_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (summary_8_constructor_28_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_27__27_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 error_0) (and (= expr_24_1 (= expr_22_0 expr_23_0)) (and (=> true true) (and (= expr_23_0 2) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 a_2_1) true))))))) true) (block_28_return_constructor_28_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_28_return_constructor_28_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_8_constructor_28_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_30_A_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_31_A_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_31_A_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_32_A_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_31_A_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_32_A_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_32_A_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_8_constructor_28_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_30_A_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_32_A_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_8_constructor_28_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_30_A_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |block_33_constructor_12_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_34__11_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_33_constructor_12_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_33_constructor_12_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_34__11_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_35_return_constructor_12_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_34__11_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_35_return_constructor_12_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_35_return_constructor_12_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_7_constructor_12_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_36_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_37_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_37_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_38_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_37_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_38_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_38_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_7_constructor_12_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_36_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_38_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_7_constructor_12_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_36_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_39_A_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) true) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_39_A_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_39_A_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_36_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_18_0) (and (=> true true) (and (= expr_18_0 2) true))))) (> error_1 0)) (summary_constructor_6_A_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_39_A_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_30_A_29_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 state_3 a_2_3) (and (= error_1 0) (and (contract_initializer_36_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_18_0) (and (=> true true) (and (= expr_18_0 2) true))))))) (> error_2 0)) (summary_constructor_6_A_29_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_39_A_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_2 0) (and (contract_initializer_30_A_29_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 state_3 a_2_3) (and (= error_1 0) (and (contract_initializer_36_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_18_0) (and (=> true true) (and (= expr_18_0 2) true)))))))) true) (summary_constructor_6_A_29_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_6_A_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_4_A_29_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |block_40_constructor_44_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_41__43_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_40_constructor_44_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_40_constructor_44_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_41__43_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_42_return_constructor_44_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_43_constructor_44_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_41__43_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= expr_40_1 (= expr_38_0 expr_39_0)) (and (=> true true) (and (= expr_39_0 3) (and (=> true (and (>= expr_38_0 0) (<= expr_38_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_0 a_2_1) true)))))) (and (not expr_40_1) (= error_1 2))) (block_43_constructor_44_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (block_43_constructor_44_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (summary_13_constructor_44_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_41__43_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 error_0) (and (= expr_40_1 (= expr_38_0 expr_39_0)) (and (=> true true) (and (= expr_39_0 3) (and (=> true (and (>= expr_38_0 0) (<= expr_38_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_0 a_2_1) true))))))) true) (block_42_return_constructor_44_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_42_return_constructor_44_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_13_constructor_44_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_44_B_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_45_B_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_45_B_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_46_B_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_45_B_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_46_B_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_46_B_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_13_constructor_44_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_44_B_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_46_B_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_13_constructor_44_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_44_B_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |block_47_constructor_12_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_48__11_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_47_constructor_12_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_47_constructor_12_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_48__11_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_49_return_constructor_12_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_48__11_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_49_return_constructor_12_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_49_return_constructor_12_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_12_constructor_12_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_50_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_51_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_51_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_52_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_51_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_52_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_52_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_12_constructor_12_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_50_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_52_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_12_constructor_12_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_50_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_53_B_45_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) true) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_53_B_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_53_B_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_50_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_34_0) (and (=> true true) (and (= expr_34_0 3) true))))) (> error_1 0)) (summary_constructor_11_B_45_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_53_B_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_44_B_45_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 state_3 a_2_3) (and (= error_1 0) (and (contract_initializer_50_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_34_0) (and (=> true true) (and (= expr_34_0 3) true))))))) (> error_2 0)) (summary_constructor_11_B_45_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_53_B_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_2 0) (and (contract_initializer_44_B_45_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 state_3 a_2_3) (and (= error_1 0) (and (contract_initializer_50_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_34_0) (and (=> true true) (and (= expr_34_0 3) true)))))))) true) (summary_constructor_11_B_45_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_11_B_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_9_B_45_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |block_54_constructor_60_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_55__59_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_54_constructor_60_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_54_constructor_60_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_55__59_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_56_return_constructor_60_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_57_constructor_60_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_55__59_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= expr_56_1 (= expr_54_0 expr_55_0)) (and (=> true true) (and (= expr_55_0 4) (and (=> true (and (>= expr_54_0 0) (<= expr_54_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_54_0 a_2_1) true)))))) (and (not expr_56_1) (= error_1 3))) (block_57_constructor_60_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (block_57_constructor_60_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (summary_18_constructor_60_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_55__59_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 error_0) (and (= expr_56_1 (= expr_54_0 expr_55_0)) (and (=> true true) (and (= expr_55_0 4) (and (=> true (and (>= expr_54_0 0) (<= expr_54_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_54_0 a_2_1) true))))))) true) (block_56_return_constructor_60_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_56_return_constructor_60_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_18_constructor_60_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_58_J_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_59_J_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_59_J_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_60_J_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_59_J_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_60_J_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_60_J_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_18_constructor_60_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_58_J_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_60_J_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_18_constructor_60_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_58_J_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |block_61_constructor_12_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_62__11_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_61_constructor_12_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_61_constructor_12_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_62__11_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_63_return_constructor_12_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_62__11_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_63_return_constructor_12_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_63_return_constructor_12_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_17_constructor_12_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_64_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_65_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_65_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_66_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_65_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_66_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_66_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_17_constructor_12_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_64_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_66_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_17_constructor_12_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_64_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_67_J_61_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) true) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_67_J_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_50_0 Int) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_67_J_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_64_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_50_0) (and (=> true true) (and (= expr_50_0 3) true))))) (> error_1 0)) (summary_constructor_16_J_61_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_50_0 Int) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_67_J_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_58_J_61_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 state_3 a_2_3) (and (= error_1 0) (and (contract_initializer_64_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_50_0) (and (=> true true) (and (= expr_50_0 3) true))))))) (> error_2 0)) (summary_constructor_16_J_61_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_50_0 Int) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_67_J_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_2 0) (and (contract_initializer_58_J_61_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 state_3 a_2_3) (and (= error_1 0) (and (contract_initializer_64_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_50_0) (and (=> true true) (and (= expr_50_0 3) true)))))))) true) (summary_constructor_16_J_61_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_50_0 Int) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_16_J_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_14_J_61_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_50_0 Int) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_6_A_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_4_0)))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_50_0 Int) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_11_B_45_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 2))) error_target_5_0)))


(declare-fun |error_target_6_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_50_0 Int) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_16_J_61_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 3))) error_target_6_0)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_18_0 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_34_0 Int) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_50_0 Int) (expr_54_0 Int) (expr_55_0 Int) (expr_56_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> error_target_6_0 false)))
(check-sat)