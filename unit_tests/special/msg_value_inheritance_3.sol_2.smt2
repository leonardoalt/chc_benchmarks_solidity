(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_A_15_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_A_15_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int))
(=> (= error_0 0) (nondet_interface_1_A_15_0 error_0 this_0 abi_0 crypto_0 state_0 x_4_0 state_0 x_4_0))))


(declare-fun |summary_3_constructor_14_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_4_B_27_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_5_B_27_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_6_B_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int))
(=> (= error_0 0) (nondet_interface_5_B_27_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_7_constructor_26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |interface_8_C_47_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_9_C_47_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_10_C_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int))
(=> (= error_0 0) (nondet_interface_9_C_47_0 error_0 this_0 abi_0 crypto_0 state_0 x_4_0 state_0 x_4_0))))


(declare-fun |summary_11_constructor_14_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_12_constructor_26_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_13_constructor_46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_14_constructor_14_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_15__13_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(block_14_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_14_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) true)) true) (block_15__13_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |block_16_return_constructor_14_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_17_constructor_14_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_15__13_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) true)))))) (and (not expr_10_1) (= error_1 1))) (block_17_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (block_17_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (summary_3_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_15__13_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 error_0) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) true))))))) true) (block_16_return_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_16_return_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) true) (summary_3_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |contract_initializer_18_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_19_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) (contract_initializer_entry_19_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |contract_initializer_after_init_20_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_entry_19_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= x_4_2 expr_3_1) (and (=> true (and (>= expr_3_1 0) (<= expr_3_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_3_1 (|msg.value| tx_0)) true)))) true) (contract_initializer_after_init_20_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_20_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (summary_3_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)) (> error_1 0)) (contract_initializer_18_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_20_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 0) (and (summary_3_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true))) true) (contract_initializer_18_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(declare-fun |implicit_constructor_entry_21_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_4_2 x_4_0))) true) (and true (= x_4_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_21_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (implicit_constructor_entry_21_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (contract_initializer_18_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)) (> error_1 0)) (summary_constructor_2_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (implicit_constructor_entry_21_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 0) (and (contract_initializer_18_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true))) true) (summary_constructor_2_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (summary_constructor_2_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_15_0 this_0 abi_0 crypto_0 state_1 x_4_1))))


(declare-fun |block_22_constructor_26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_23__25_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(block_22_constructor_26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (block_22_constructor_26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_23__25_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_24_return_constructor_26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_25_constructor_26_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (block_23__25_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_22_1 (>= expr_20_1 expr_21_0)) (and (=> true true) (and (= expr_21_0 0) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_1 (|msg.value| tx_0)) true)))))) (and (not expr_22_1) (= error_1 2))) (block_25_constructor_26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (block_25_constructor_26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_7_constructor_26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (block_23__25_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 error_0) (and (= expr_22_1 (>= expr_20_1 expr_21_0)) (and (=> true true) (and (= expr_21_0 0) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_1 (|msg.value| tx_0)) true))))))) true) (block_24_return_constructor_26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (block_24_return_constructor_26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_7_constructor_26_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_26_B_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_27_B_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (contract_initializer_entry_27_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_28_B_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (contract_initializer_entry_27_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_28_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (contract_initializer_after_init_28_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_7_constructor_26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (contract_initializer_26_B_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (contract_initializer_after_init_28_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (summary_7_constructor_26_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (contract_initializer_26_B_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(declare-fun |implicit_constructor_entry_29_B_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) true) true) true) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_29_B_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (implicit_constructor_entry_29_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_26_B_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_6_B_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (implicit_constructor_entry_29_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_26_B_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_6_B_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (summary_constructor_6_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= error_0 0))) (interface_4_B_27_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_30_constructor_46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_31__45_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_30_constructor_46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_30_constructor_46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) true)) true) (block_31__45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |block_32_return_constructor_46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_33_constructor_46_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_31__45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= expr_42_1 (>= expr_40_1 expr_41_0)) (and (=> true true) (and (= expr_41_0 0) (and (=> true (and (>= expr_40_1 0) (<= expr_40_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_1 (|msg.value| tx_0)) true)))))) (and (not expr_42_1) (= error_1 3))) (block_33_constructor_46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (block_33_constructor_46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (summary_13_constructor_46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_31__45_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 error_0) (and (= expr_42_1 (>= expr_40_1 expr_41_0)) (and (=> true true) (and (= expr_41_0 0) (and (=> true (and (>= expr_40_1 0) (<= expr_40_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_40_1 (|msg.value| tx_0)) true))))))) true) (block_32_return_constructor_46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_32_return_constructor_46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) true) (summary_13_constructor_46_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |contract_initializer_34_C_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_35_C_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) (contract_initializer_entry_35_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |contract_initializer_after_init_36_C_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_35_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) true) (contract_initializer_after_init_36_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_36_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (summary_13_constructor_46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)) (> error_1 0)) (contract_initializer_34_C_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_36_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 0) (and (summary_13_constructor_46_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true))) true) (contract_initializer_34_C_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(declare-fun |block_37_constructor_26_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_38__25_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_37_constructor_26_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_37_constructor_26_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) true)) true) (block_38__25_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |block_39_return_constructor_26_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_40_constructor_26_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_38__25_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= expr_22_1 (>= expr_20_1 expr_21_0)) (and (=> true true) (and (= expr_21_0 0) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_1 (|msg.value| tx_0)) true)))))) (and (not expr_22_1) (= error_1 4))) (block_40_constructor_26_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (block_40_constructor_26_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (summary_12_constructor_26_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_38__25_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 error_0) (and (= expr_22_1 (>= expr_20_1 expr_21_0)) (and (=> true true) (and (= expr_21_0 0) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_1 (|msg.value| tx_0)) true))))))) true) (block_39_return_constructor_26_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_39_return_constructor_26_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) true) (summary_12_constructor_26_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |contract_initializer_41_B_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_42_B_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (contract_initializer_entry_42_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_43_B_27_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_42_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_43_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_43_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_12_constructor_26_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)) (> error_1 0)) (contract_initializer_41_B_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_43_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (summary_12_constructor_26_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true))) true) (contract_initializer_41_B_27_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(declare-fun |block_44_constructor_14_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_45__13_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(block_44_constructor_14_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_44_constructor_14_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) true)) true) (block_45__13_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |block_46_return_constructor_14_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_47_constructor_14_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_45__13_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) true)))))) (and (not expr_10_1) (= error_1 5))) (block_47_constructor_14_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (block_47_constructor_14_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (summary_11_constructor_14_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_45__13_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 error_0) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) true))))))) true) (block_46_return_constructor_14_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (block_46_return_constructor_14_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) true) (summary_11_constructor_14_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |contract_initializer_48_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_49_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) (contract_initializer_entry_49_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |contract_initializer_after_init_50_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_entry_49_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= x_4_2 expr_3_1) (and (=> true (and (>= expr_3_1 0) (<= expr_3_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_3_1 (|msg.value| tx_0)) true)))) true) (contract_initializer_after_init_50_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_50_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (summary_11_constructor_14_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)) (> error_1 0)) (contract_initializer_48_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (contract_initializer_after_init_50_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 0) (and (summary_11_constructor_14_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true))) true) (contract_initializer_48_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(declare-fun |implicit_constructor_entry_51_C_47_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_4_2 x_4_0))) true) (and true (= x_4_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_51_C_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_51_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (contract_initializer_48_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)) (> error_1 0)) (summary_constructor_10_C_47_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_51_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (contract_initializer_41_B_27_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_48_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)))) (> error_2 0)) (summary_constructor_10_C_47_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_3 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_51_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (contract_initializer_34_C_47_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_4_2 state_4 x_4_3) (and (= error_2 0) (and (contract_initializer_41_B_27_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_48_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)))))) (> error_3 0)) (summary_constructor_10_C_47_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_4 x_4_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (implicit_constructor_entry_51_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_3 0) (and (contract_initializer_34_C_47_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 x_4_2 state_4 x_4_3) (and (= error_2 0) (and (contract_initializer_41_B_27_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= error_1 0) (and (contract_initializer_48_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true))))))) true) (summary_constructor_10_C_47_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_4 x_4_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_10_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= error_0 0))) (interface_8_C_47_0 this_0 abi_0 crypto_0 state_1 x_4_1))))


(declare-fun |error_target_6_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_2_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_6_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_10_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= error_0 1))) error_target_6_0)))


(declare-fun |error_target_7_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_6_B_27_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= error_0 2))) error_target_7_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_10_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= error_0 2))) error_target_7_0)))


(declare-fun |error_target_8_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_10_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= error_0 3))) error_target_8_0)))


(declare-fun |error_target_9_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> (and (and (summary_constructor_10_C_47_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= error_0 4))) error_target_9_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_3_1 Int) (expr_40_1 Int) (expr_41_0 Int) (expr_42_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int) (x_4_4 Int) (x_4_5 Int))
(=> error_target_9_0 false)))
(check-sat)