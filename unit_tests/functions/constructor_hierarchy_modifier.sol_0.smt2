(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_23_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_23_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_23_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_3_constructor_22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |interface_4_A_47_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_5_A_47_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_6_A_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_5_A_47_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_7_constructor_22_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_8_constructor_46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_9_constructor_22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_10__21_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int))
(block_9_constructor_22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int))
(=> (and (and (block_9_constructor_22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_12_1 x_12_0))) true)) true) (block_10__21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1))))


(declare-fun |block_11_return__10_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_12_return_constructor_22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int))
(=> (and (and (block_10__21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) (and (= a_2_2 expr_19_1) (and (=> true (and (>= expr_19_1 0) (<= expr_19_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_1 expr_18_0) (and (=> true (and (>= expr_17_0 0) (<= expr_17_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_0 a_2_1) (and (=> true (and (>= expr_18_0 0) (<= expr_18_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_0 x_12_1) (and (and (>= x_12_1 0) (<= x_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_12_return_constructor_22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_2 x_12_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int))
(=> (and (and (block_12_return_constructor_22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 7) true)))))))) true) (block_11_return__10_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_2 x_12_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int))
(=> (and (and (block_11_return__10_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) true) true) (summary_3_constructor_22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1))))


(declare-fun |contract_initializer_13_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_14_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_12_1 x_12_0))) (contract_initializer_entry_14_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1))))


(declare-fun |contract_initializer_after_init_15_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int))
(=> (and (and (contract_initializer_entry_14_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) true) true) (contract_initializer_after_init_15_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int))
(=> (and (and (contract_initializer_after_init_15_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) (and (summary_3_constructor_22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_12_1 state_2 a_2_2 x_12_2) true)) (> error_1 0)) (contract_initializer_13_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_2 a_2_2 x_12_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int))
(=> (and (and (contract_initializer_after_init_15_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) (and (= error_1 0) (and (summary_3_constructor_22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_12_1 state_2 a_2_2 x_12_2) true))) true) (contract_initializer_13_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_2 a_2_2 x_12_2))))


(declare-fun |implicit_constructor_entry_16_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= x_12_2 x_12_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_16_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_2 a_2_2 x_12_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int))
(=> (and (and (implicit_constructor_entry_16_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_2) (and (contract_initializer_13_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_12_2 state_2 a_2_2 x_12_3) true)) (> error_1 0)) (summary_constructor_2_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_2 a_2_2 x_12_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int))
(=> (and (and (implicit_constructor_entry_16_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_2) (and (= error_1 0) (and (contract_initializer_13_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_12_2 state_2 a_2_2 x_12_3) true))) true) (summary_constructor_2_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_2 a_2_2 x_12_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int))
(=> (and (and (summary_constructor_2_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_23_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |block_17_constructor_46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_18__45_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(block_17_constructor_46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (block_17_constructor_46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) true)) true) (block_18__45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |block_19_return_constructor_46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_20_constructor_46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (block_18__45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= expr_42_1 (= expr_40_0 expr_41_0)) (and (=> true true) (and (= expr_41_0 4) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_0 a_2_1) true)))))) (and (not expr_42_1) (= error_1 1))) (block_20_constructor_46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (block_20_constructor_46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (summary_8_constructor_46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (block_18__45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 error_0) (and (= expr_42_1 (= expr_40_0 expr_41_0)) (and (=> true true) (and (= expr_41_0 4) (and (=> true (and (>= expr_40_0 0) (<= expr_40_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_0 a_2_1) true))))))) true) (block_19_return_constructor_46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (block_19_return_constructor_46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (summary_8_constructor_46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_21_A_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_22_A_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) true) (contract_initializer_entry_22_A_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(declare-fun |contract_initializer_after_init_23_A_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (contract_initializer_entry_22_A_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) true) (contract_initializer_after_init_23_A_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (contract_initializer_after_init_23_A_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (summary_8_constructor_46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true)) (> error_1 0)) (contract_initializer_21_A_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (contract_initializer_after_init_23_A_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_1 0) (and (summary_8_constructor_46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 state_2 a_2_2) true))) true) (contract_initializer_21_A_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(declare-fun |block_24_constructor_22_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_25__21_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(block_24_constructor_22_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (block_24_constructor_22_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_12_1 x_12_0))) true)) true) (block_25__21_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1))))


(declare-fun |block_26_return__10_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_27_return_constructor_22_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (block_25__21_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) (and (= a_2_2 expr_19_1) (and (=> true (and (>= expr_19_1 0) (<= expr_19_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_1 expr_18_0) (and (=> true (and (>= expr_17_0 0) (<= expr_17_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_0 a_2_1) (and (=> true (and (>= expr_18_0 0) (<= expr_18_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_18_0 x_12_1) (and (and (>= x_12_1 0) (<= x_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_27_return_constructor_22_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_2 x_12_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (block_27_return_constructor_22_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) (and (= a_2_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 expr_6_0) (and (=> true (and (>= expr_5_0 0) (<= expr_5_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_5_0 a_2_1) (and (=> true true) (and (= expr_6_0 7) true)))))))) true) (block_26_return__10_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_2 x_12_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (block_26_return__10_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) true) true) (summary_7_constructor_22_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1))))


(declare-fun |contract_initializer_28_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_29_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_12_1 x_12_0))) (contract_initializer_entry_29_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1))))


(declare-fun |contract_initializer_after_init_30_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (contract_initializer_entry_29_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) true) true) (contract_initializer_after_init_30_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (contract_initializer_after_init_30_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) (and (summary_7_constructor_22_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_12_1 state_2 a_2_2 x_12_2) true)) (> error_1 0)) (contract_initializer_28_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_2 a_2_2 x_12_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (contract_initializer_after_init_30_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_1 a_2_1 x_12_1) (and (= error_1 0) (and (summary_7_constructor_22_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_12_1 state_2 a_2_2 x_12_2) true))) true) (contract_initializer_28_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_12_0 state_2 a_2_2 x_12_2))))


(declare-fun |implicit_constructor_entry_31_A_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) true) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_31_A_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_36_0 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (implicit_constructor_entry_31_A_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_28_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_12_2 state_2 a_2_2 x_12_3) (and (= x_12_2 expr_36_0) (and (=> true true) (and (= expr_36_0 2) true))))) (> error_1 0)) (summary_constructor_6_A_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_2 a_2_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_36_0 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (implicit_constructor_entry_31_A_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (contract_initializer_21_A_47_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 state_3 a_2_3) (and (= error_1 0) (and (contract_initializer_28_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_12_2 state_2 a_2_2 x_12_3) (and (= x_12_2 expr_36_0) (and (=> true true) (and (= expr_36_0 2) true))))))) (> error_2 0)) (summary_constructor_6_A_47_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_36_0 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (implicit_constructor_entry_31_A_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) (and (= error_2 0) (and (contract_initializer_21_A_47_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 state_3 a_2_3) (and (= error_1 0) (and (contract_initializer_28_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_12_2 state_2 a_2_2 x_12_3) (and (= x_12_2 expr_36_0) (and (=> true true) (and (= expr_36_0 2) true)))))))) true) (summary_constructor_6_A_47_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_3 a_2_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_36_0 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (summary_constructor_6_A_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_4_A_47_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |error_target_2_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_36_0 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> (and (and (summary_constructor_6_A_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 state_1 a_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_2_0)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_17_0 Int) (expr_18_0 Int) (expr_19_1 Int) (expr_36_0 Int) (expr_40_0 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_12_0 Int) (x_12_1 Int) (x_12_2 Int) (x_12_3 Int) (x_12_4 Int) (x_12_5 Int))
(=> error_target_2_0 false)))
(check-sat)