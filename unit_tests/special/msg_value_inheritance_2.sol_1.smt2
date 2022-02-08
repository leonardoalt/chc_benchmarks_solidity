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
(declare-fun |interface_4_C_34_0| (Int |abi_type| |crypto_type| |state_type| Int Int ) Bool)
(declare-fun |nondet_interface_5_C_34_0| (Int Int |abi_type| |crypto_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_constructor_6_C_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (x_4_0 Int))
(=> (= error_0 0) (nondet_interface_5_C_34_0 error_0 this_0 abi_0 crypto_0 state_0 v_21_0 x_4_0 state_0 v_21_0 x_4_0))))


(declare-fun |summary_7_constructor_14_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_8_constructor_33_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_9_constructor_14_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_10__13_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int))
(block_9_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_9_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) true)) true) (block_10__13_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |block_11_return_constructor_14_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_12_constructor_14_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_10__13_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) true)))))) (and (not expr_10_1) (= error_1 1))) (block_12_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int))
(=> (block_12_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (summary_3_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_10__13_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 error_0) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) true))))))) true) (block_11_return_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (block_11_return_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) true) (summary_3_constructor_14_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |contract_initializer_13_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_14_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) (contract_initializer_entry_14_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |contract_initializer_after_init_15_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_entry_14_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= x_4_2 expr_3_1) (and (=> true (and (>= expr_3_1 0) (<= expr_3_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_3_1 (|msg.value| tx_0)) true)))) true) (contract_initializer_after_init_15_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_15_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (summary_3_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)) (> error_1 0)) (contract_initializer_13_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_15_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 0) (and (summary_3_constructor_14_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true))) true) (contract_initializer_13_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(declare-fun |implicit_constructor_entry_16_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_4_2 x_4_0))) true) (and true (= x_4_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_16_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (implicit_constructor_entry_16_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (contract_initializer_13_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)) (> error_1 0)) (summary_constructor_2_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (implicit_constructor_entry_16_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 0) (and (contract_initializer_13_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true))) true) (summary_constructor_2_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (summary_constructor_2_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_15_0 this_0 abi_0 crypto_0 state_1 x_4_1))))


(declare-fun |block_17_constructor_33_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_18__32_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(block_17_constructor_33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (block_17_constructor_33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= v_21_1 v_21_0)) (= x_4_1 x_4_0))) true) true)) true) (block_18__32_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1))))


(declare-fun |block_19_return_constructor_33_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_20_constructor_33_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (block_18__32_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 0) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 v_21_1) true)))))) (and (not expr_29_1) (= error_1 2))) (block_20_constructor_33_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (block_20_constructor_33_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (summary_8_constructor_33_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (block_18__32_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (and (= error_1 error_0) (and (= expr_29_1 (= expr_27_0 expr_28_0)) (and (=> true true) (and (= expr_28_0 0) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 v_21_1) true))))))) true) (block_19_return_constructor_33_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (block_19_return_constructor_33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) true) true) (summary_8_constructor_33_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1))))


(declare-fun |contract_initializer_21_C_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_22_C_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= v_21_1 v_21_0)) (= x_4_1 x_4_0))) true) (contract_initializer_entry_22_C_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1))))


(declare-fun |contract_initializer_after_init_23_C_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (contract_initializer_entry_22_C_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (and (= v_21_2 expr_20_1) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_1 (|msg.value| tx_0)) true)))) true) (contract_initializer_after_init_23_C_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_2 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (contract_initializer_after_init_23_C_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (and (summary_8_constructor_33_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 v_21_1 x_4_1 state_2 v_21_2 x_4_2) true)) (> error_1 0)) (contract_initializer_21_C_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_2 v_21_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (contract_initializer_after_init_23_C_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (and (= error_1 0) (and (summary_8_constructor_33_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 v_21_1 x_4_1 state_2 v_21_2 x_4_2) true))) true) (contract_initializer_21_C_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_2 v_21_2 x_4_2))))


(declare-fun |block_24_constructor_14_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_25__13_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(block_24_constructor_14_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (block_24_constructor_14_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= v_21_1 v_21_0)) (= x_4_1 x_4_0))) true) true)) true) (block_25__13_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1))))


(declare-fun |block_26_return_constructor_14_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_27_constructor_14_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (block_25__13_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) true)))))) (and (not expr_10_1) (= error_1 3))) (block_27_constructor_14_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (block_27_constructor_14_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (summary_7_constructor_14_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (block_25__13_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (and (= error_1 error_0) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_4_1) true))))))) true) (block_26_return_constructor_14_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (block_26_return_constructor_14_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) true) true) (summary_7_constructor_14_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1))))


(declare-fun |contract_initializer_28_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_29_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) (contract_initializer_entry_29_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |contract_initializer_after_init_30_A_15_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (contract_initializer_entry_29_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= x_4_2 expr_3_1) (and (=> true (and (>= expr_3_1 0) (<= expr_3_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_3_1 (|msg.value| tx_0)) true)))) true) (contract_initializer_after_init_30_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (contract_initializer_after_init_30_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (summary_7_constructor_14_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 v_21_1 x_4_1 state_2 v_21_2 x_4_2) true)) (> error_1 0)) (contract_initializer_28_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (contract_initializer_after_init_30_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 0) (and (summary_7_constructor_14_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 v_21_1 x_4_1 state_2 v_21_2 x_4_2) true))) true) (contract_initializer_28_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(declare-fun |implicit_constructor_entry_31_C_34_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and (and true (= v_21_2 v_21_0)) (= x_4_2 x_4_0))) true) (and (and true (= v_21_2 0)) (= x_4_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_31_C_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_2 v_21_2 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (implicit_constructor_entry_31_C_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (and (contract_initializer_28_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)) (> error_1 0)) (summary_constructor_6_C_34_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_2 v_21_1 x_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (implicit_constructor_entry_31_C_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (and (contract_initializer_21_C_34_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 v_21_1 x_4_2 state_3 v_21_2 x_4_3) (and (= error_1 0) (and (contract_initializer_28_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)))) (> error_2 0)) (summary_constructor_6_C_34_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_3 v_21_2 x_4_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (implicit_constructor_entry_31_C_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) (and (= error_2 0) (and (contract_initializer_21_C_34_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 v_21_1 x_4_2 state_3 v_21_2 x_4_3) (and (= error_1 0) (and (contract_initializer_28_A_15_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true))))) true) (summary_constructor_6_C_34_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_3 v_21_2 x_4_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (summary_constructor_6_C_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= error_0 0))) (interface_4_C_34_0 this_0 abi_0 crypto_0 state_1 v_21_1 x_4_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (summary_constructor_2_A_15_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_4_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (summary_constructor_6_C_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= error_0 1))) error_target_4_0)))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> (and (and (summary_constructor_6_C_34_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 v_21_0 x_4_0 state_1 v_21_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= error_0 2))) error_target_5_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_20_1 Int) (expr_27_0 Int) (expr_28_0 Int) (expr_29_1 Bool) (expr_3_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_21_0 Int) (v_21_1 Int) (v_21_2 Int) (v_21_3 Int) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int) (x_4_3 Int))
(=> error_target_5_0 false)))
(check-sat)