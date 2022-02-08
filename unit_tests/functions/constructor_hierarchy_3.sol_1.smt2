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
(declare-fun |interface_4_B_26_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_5_B_26_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_6_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_5_B_26_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_7_constructor_12_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_8_constructor_25_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |interface_9_A_57_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_10_A_57_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_11_A_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_10_A_57_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 state_0 a_2_0))))


(declare-fun |summary_12_constructor_12_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_13_constructor_25_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_14_constructor_56_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_15_constructor_12_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_16__11_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_1 Int) (x_30_1 Int) (x_4_0 Int) (x_4_1 Int))
(block_15_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_1 Int) (x_30_1 Int) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_15_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_16__11_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_17_return_constructor_12_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_1 Int) (x_30_1 Int) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_16__11_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_17_return_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_1 Int) (x_30_1 Int) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_17_return_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_3_constructor_12_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_18_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_19_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_1 Int) (x_30_1 Int) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_19_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_20_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_1 Int) (x_30_1 Int) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (contract_initializer_entry_19_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_20_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_1 Int) (x_30_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_20_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_3_constructor_12_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_18_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_1 Int) (x_30_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_20_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_3_constructor_12_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_18_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_21_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_1 Int) (x_30_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= x_4_2 x_4_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_21_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_1 Int) (x_30_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (implicit_constructor_entry_21_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_2) (and (contract_initializer_18_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)) (> error_1 0)) (summary_constructor_2_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_1 Int) (x_30_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (implicit_constructor_entry_21_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_2) (and (= error_1 0) (and (contract_initializer_18_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true))) true) (summary_constructor_2_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_1 Int) (x_30_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (summary_constructor_2_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_13_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |block_22_constructor_25_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_23__24_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_22_constructor_25_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_22_constructor_25_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_17_1 x_17_0))) true)) true) (block_23__24_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1))))


(declare-fun |block_24_return_constructor_25_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_23__24_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1) (and (= a_2_2 expr_22_1) (and (=> true (and (>= expr_22_1 0) (<= expr_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_1 expr_21_0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 a_2_1) (and (=> true (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 x_17_1) (and (and (>= x_17_1 0) (<= x_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_24_return_constructor_25_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_2 x_17_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_24_return_constructor_25_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1) true) true) (summary_8_constructor_25_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1))))


(declare-fun |contract_initializer_25_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_26_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_17_1 x_17_0))) (contract_initializer_entry_26_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1))))


(declare-fun |contract_initializer_after_init_27_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_26_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1) true) true) (contract_initializer_after_init_27_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_27_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1) (and (summary_8_constructor_25_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_17_1 state_2 a_2_2 x_17_2) true)) (> error_1 0)) (contract_initializer_25_B_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_2 a_2_2 x_17_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_27_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1) (and (= error_1 0) (and (summary_8_constructor_25_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_17_1 state_2 a_2_2 x_17_2) true))) true) (contract_initializer_25_B_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_2 a_2_2 x_17_2))))


(declare-fun |block_28_constructor_12_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_29__11_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_28_constructor_12_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_28_constructor_12_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_29__11_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_30_return_constructor_12_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_29__11_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_30_return_constructor_12_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_30_return_constructor_12_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_7_constructor_12_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_31_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_32_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_32_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_33_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_32_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_33_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_33_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_7_constructor_12_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_31_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_33_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_7_constructor_12_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_31_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_34_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= x_17_2 x_17_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_34_B_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_2 a_2_2 x_17_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_34_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_2) (and (contract_initializer_31_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)) (> error_1 0)) (summary_constructor_6_B_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_2 a_2_2 x_17_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_34_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_2) (and (contract_initializer_25_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 x_17_2 state_3 a_2_3 x_17_3) (and (= error_1 0) (and (contract_initializer_31_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true)))) (> error_2 0)) (summary_constructor_6_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_3 a_2_3 x_17_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_34_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_2) (and (= error_2 0) (and (contract_initializer_25_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 x_17_2 state_3 a_2_3 x_17_3) (and (= error_1 0) (and (contract_initializer_31_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) true))))) true) (summary_constructor_6_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_3 a_2_3 x_17_3))))


(declare-fun |block_35_constructor_56_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_36__55_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_35_constructor_56_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_35_constructor_56_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_30_1 x_30_0))) true)) true) (block_36__55_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1))))


(declare-fun |block_37_return_constructor_56_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_38_constructor_56_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_36__55_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1) (and (= expr_44_1 (= expr_42_0 expr_43_0)) (and (=> true (and (>= expr_43_0 0) (<= expr_43_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_43_0 x_30_1) (and (=> true (and (>= expr_42_0 0) (<= expr_42_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_42_0 a_2_1) (and (and (>= x_30_1 0) (<= x_30_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))) (and (not expr_44_1) (= error_1 1))) (block_38_constructor_56_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (block_38_constructor_56_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1) (summary_14_constructor_56_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1))))


(declare-fun |block_39_constructor_56_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_36__55_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1) (and (= expr_52_1 (= expr_48_0 expr_51_1)) (and (=> true (and (>= expr_51_1 0) (<= expr_51_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_51_1 (+ expr_49_0 expr_50_0)) (and (=> true true) (and (= expr_50_0 1) (and (=> true (and (>= expr_49_0 0) (<= expr_49_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_49_0 x_30_1) (and (=> true (and (>= expr_48_0 0) (<= expr_48_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_48_0 a_2_1) (and (= error_1 error_0) (and (= expr_44_1 (= expr_42_0 expr_43_0)) (and (=> true (and (>= expr_43_0 0) (<= expr_43_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_43_0 x_30_1) (and (=> true (and (>= expr_42_0 0) (<= expr_42_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_42_0 a_2_1) (and (and (>= x_30_1 0) (<= x_30_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))))))))))) (and (not expr_52_1) (= error_2 2))) (block_39_constructor_56_57_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (block_39_constructor_56_57_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1) (summary_14_constructor_56_57_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_36__55_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1) (and (= error_2 error_1) (and (= expr_52_1 (= expr_48_0 expr_51_1)) (and (=> true (and (>= expr_51_1 0) (<= expr_51_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_51_1 (+ expr_49_0 expr_50_0)) (and (=> true true) (and (= expr_50_0 1) (and (=> true (and (>= expr_49_0 0) (<= expr_49_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_49_0 x_30_1) (and (=> true (and (>= expr_48_0 0) (<= expr_48_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_48_0 a_2_1) (and (= error_1 error_0) (and (= expr_44_1 (= expr_42_0 expr_43_0)) (and (=> true (and (>= expr_43_0 0) (<= expr_43_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_43_0 x_30_1) (and (=> true (and (>= expr_42_0 0) (<= expr_42_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_42_0 a_2_1) (and (and (>= x_30_1 0) (<= x_30_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))))))))) true) (block_37_return_constructor_56_57_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_37_return_constructor_56_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1) true) true) (summary_14_constructor_56_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1))))


(declare-fun |contract_initializer_40_A_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_41_A_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_30_1 x_30_0))) (contract_initializer_entry_41_A_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1))))


(declare-fun |contract_initializer_after_init_42_A_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_41_A_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1) true) true) (contract_initializer_after_init_42_A_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_42_A_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1) (and (summary_14_constructor_56_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_30_1 state_2 a_2_2 x_30_2) true)) (> error_1 0)) (contract_initializer_40_A_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_2 a_2_2 x_30_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_42_A_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_1) (and (= error_1 0) (and (summary_14_constructor_56_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_30_1 state_2 a_2_2 x_30_2) true))) true) (contract_initializer_40_A_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_2 a_2_2 x_30_2))))


(declare-fun |block_43_constructor_25_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_44__24_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_43_constructor_25_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_43_constructor_25_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_17_1 x_17_0))) true)) true) (block_44__24_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1))))


(declare-fun |block_45_return_constructor_25_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_44__24_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1) (and (= a_2_2 expr_22_1) (and (=> true (and (>= expr_22_1 0) (<= expr_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_1 expr_21_0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 a_2_1) (and (=> true (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 x_17_1) (and (and (>= x_17_1 0) (<= x_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_45_return_constructor_25_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_2 x_17_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_45_return_constructor_25_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1) true) true) (summary_13_constructor_25_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1))))


(declare-fun |contract_initializer_46_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_47_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_17_1 x_17_0))) (contract_initializer_entry_47_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1))))


(declare-fun |contract_initializer_after_init_48_B_26_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_47_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1) true) true) (contract_initializer_after_init_48_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_48_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1) (and (summary_13_constructor_25_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_17_1 state_2 a_2_2 x_17_2) true)) (> error_1 0)) (contract_initializer_46_B_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_2 a_2_2 x_17_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_48_B_26_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_1 a_2_1 x_17_1) (and (= error_1 0) (and (summary_13_constructor_25_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_17_1 state_2 a_2_2 x_17_2) true))) true) (contract_initializer_46_B_26_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_17_0 state_2 a_2_2 x_17_2))))


(declare-fun |block_49_constructor_12_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_50__11_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_49_constructor_12_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_49_constructor_12_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) true)) true) (block_50__11_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |block_51_return_constructor_12_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_50__11_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= a_2_2 expr_9_1) (and (=> true (and (>= expr_9_1 0) (<= expr_9_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_1 expr_8_0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_0 a_2_1) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) (and (and (>= x_4_1 0) (<= x_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))) true) (block_51_return_constructor_12_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_2 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_51_return_constructor_12_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (summary_12_constructor_12_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_52_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_53_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= a_2_1 a_2_0))) (and true (= x_4_1 x_4_0))) (contract_initializer_entry_53_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(declare-fun |contract_initializer_after_init_54_C_13_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_53_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) true) true) (contract_initializer_after_init_54_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_54_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (summary_12_constructor_12_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true)) (> error_1 0)) (contract_initializer_52_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_54_C_13_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_1 a_2_1 x_4_1) (and (= error_1 0) (and (summary_12_constructor_12_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_1 state_2 a_2_2 x_4_2) true))) true) (contract_initializer_52_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_4_0 state_2 a_2_2 x_4_2))))


(declare-fun |implicit_constructor_entry_55_A_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= a_2_2 a_2_0))) (and true (= x_30_2 x_30_0))) (and true (= a_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_55_A_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_2 a_2_2 x_30_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_33_0 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_55_A_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_2) (and (contract_initializer_52_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_38_1) (and (=> true (and (>= expr_38_1 0) (<= expr_38_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_1 (+ expr_36_0 expr_37_0)) (and (=> true true) (and (= expr_37_0 2) (and (=> true (and (>= expr_36_0 0) (<= expr_36_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_36_0 x_30_2) (and (= x_17_2 expr_33_0) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 x_30_2) true)))))))))))) (> error_1 0)) (summary_constructor_11_A_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_2 a_2_2 x_30_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_33_0 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_55_A_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_2) (and (contract_initializer_46_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 x_17_2 state_3 a_2_3 x_17_3) (and (= error_1 0) (and (contract_initializer_52_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_38_1) (and (=> true (and (>= expr_38_1 0) (<= expr_38_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_1 (+ expr_36_0 expr_37_0)) (and (=> true true) (and (= expr_37_0 2) (and (=> true (and (>= expr_36_0 0) (<= expr_36_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_36_0 x_30_2) (and (= x_17_2 expr_33_0) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 x_30_2) true)))))))))))))) (> error_2 0)) (summary_constructor_11_A_57_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_3 a_2_3 x_30_2))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_33_0 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_55_A_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_2) (and (contract_initializer_40_A_57_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 x_30_2 state_4 a_2_4 x_30_3) (and (= error_2 0) (and (contract_initializer_46_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 x_17_2 state_3 a_2_3 x_17_3) (and (= error_1 0) (and (contract_initializer_52_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_38_1) (and (=> true (and (>= expr_38_1 0) (<= expr_38_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_1 (+ expr_36_0 expr_37_0)) (and (=> true true) (and (= expr_37_0 2) (and (=> true (and (>= expr_36_0 0) (<= expr_36_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_36_0 x_30_2) (and (= x_17_2 expr_33_0) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 x_30_2) true)))))))))))))))) (> error_3 0)) (summary_constructor_11_A_57_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_4 a_2_4 x_30_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_33_0 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_55_A_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_2) (and (= error_3 0) (and (contract_initializer_40_A_57_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 a_2_3 x_30_2 state_4 a_2_4 x_30_3) (and (= error_2 0) (and (contract_initializer_46_B_26_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 a_2_2 x_17_2 state_3 a_2_3 x_17_3) (and (= error_1 0) (and (contract_initializer_52_C_13_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 x_4_2 state_2 a_2_2 x_4_3) (and (= x_4_2 expr_38_1) (and (=> true (and (>= expr_38_1 0) (<= expr_38_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_1 (+ expr_36_0 expr_37_0)) (and (=> true true) (and (= expr_37_0 2) (and (=> true (and (>= expr_36_0 0) (<= expr_36_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_36_0 x_30_2) (and (= x_17_2 expr_33_0) (and (=> true (and (>= expr_33_0 0) (<= expr_33_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_33_0 x_30_2) true))))))))))))))))) true) (summary_constructor_11_A_57_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_4 a_2_4 x_30_3))))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_33_0 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_11_A_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_9_A_57_0 this_0 abi_0 crypto_0 state_1 a_2_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_33_0 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_11_A_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 x_30_0 state_1 a_2_1 x_30_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (a_2_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Int) (expr_33_0 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (expr_48_0 Int) (expr_49_0 Int) (expr_50_0 Int) (expr_51_1 Int) (expr_52_1 Bool) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_17_0 Int) (x_17_1 Int) (x_17_2 Int) (x_17_3 Int) (x_17_4 Int) (x_17_5 Int) (x_30_0 Int) (x_30_1 Int) (x_30_2 Int) (x_30_3 Int) (x_30_4 Int) (x_30_5 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> error_target_3_0 false)))
(check-sat)