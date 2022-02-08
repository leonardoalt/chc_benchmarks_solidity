(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_A_19_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_A_19_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_1_A_19_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_3_constructor_18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |interface_4_B_35_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_5_B_35_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_6_B_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_5_B_35_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_7_constructor_18_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_8_constructor_34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |interface_9_C_48_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_10_C_48_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_11_C_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_10_C_48_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_12_constructor_18_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_13_constructor_34_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_14_function_f__47_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_15_function_f__47_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_10_C_48_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_0 0) (summary_15_function_f__47_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_10_C_48_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_16_constructor_18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_17__17_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int))
(block_16_constructor_18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int))
(=> (and (and (block_16_constructor_18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= y_4_1 y_4_0))) true)) true) (block_17__17_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(declare-fun |block_18_return_constructor_18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_19_constructor_18_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int))
(=> (and (and (block_17__17_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_2_1) (and (and (>= y_4_1 0) (<= y_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))) (and (not expr_10_1) (= error_1 1))) (block_19_constructor_18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int))
(=> (block_19_constructor_18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (summary_3_constructor_18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int))
(=> (and (and (block_17__17_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (= x_2_2 expr_15_1) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 expr_14_0) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 x_2_1) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 y_4_1) (and (= error_1 error_0) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_2_1) (and (and (>= y_4_1 0) (<= y_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))))))))) true) (block_18_return_constructor_18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_2 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int))
(=> (and (and (block_18_return_constructor_18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) true) true) (summary_3_constructor_18_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(declare-fun |contract_initializer_20_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_21_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= y_4_1 y_4_0))) (contract_initializer_entry_21_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(declare-fun |contract_initializer_after_init_22_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int))
(=> (and (and (contract_initializer_entry_21_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) true) true) (contract_initializer_after_init_22_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int))
(=> (and (and (contract_initializer_after_init_22_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (summary_3_constructor_18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_1 state_2 x_2_2 y_4_2) true)) (> error_1 0)) (contract_initializer_20_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int))
(=> (and (and (contract_initializer_after_init_22_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (= error_1 0) (and (summary_3_constructor_18_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_1 state_2 x_2_2 y_4_2) true))) true) (contract_initializer_20_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_2))))


(declare-fun |implicit_constructor_entry_23_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_2_2 x_2_0))) (and true (= y_4_2 y_4_0))) (and true (= x_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_23_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int))
(=> (and (and (implicit_constructor_entry_23_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_2) (and (contract_initializer_20_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_2 state_2 x_2_2 y_4_3) true)) (> error_1 0)) (summary_constructor_2_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int))
(=> (and (and (implicit_constructor_entry_23_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_2) (and (= error_1 0) (and (contract_initializer_20_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_2 state_2 x_2_2 y_4_3) true))) true) (summary_constructor_2_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int))
(=> (and (and (summary_constructor_2_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_19_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_24_constructor_34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_25__33_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(block_24_constructor_34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_24_constructor_34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_25__33_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_26_return_constructor_34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_27_constructor_34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_25__33_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_30_1 (= expr_28_0 expr_29_0)) (and (=> true true) (and (= expr_29_0 2) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_0 x_2_1) true)))))) (and (not expr_30_1) (= error_1 2))) (block_27_constructor_34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (block_27_constructor_34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_8_constructor_34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_25__33_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 error_0) (and (= expr_30_1 (= expr_28_0 expr_29_0)) (and (=> true true) (and (= expr_29_0 2) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_0 x_2_1) true))))))) true) (block_26_return_constructor_34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_26_return_constructor_34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_8_constructor_34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_28_B_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_29_B_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) (contract_initializer_entry_29_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_after_init_30_B_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_entry_29_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (contract_initializer_after_init_30_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_after_init_30_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_8_constructor_34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (contract_initializer_28_B_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_after_init_30_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_8_constructor_34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (contract_initializer_28_B_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_31_constructor_18_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_32__17_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(block_31_constructor_18_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_31_constructor_18_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= y_4_1 y_4_0))) true)) true) (block_32__17_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(declare-fun |block_33_return_constructor_18_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_34_constructor_18_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_32__17_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_2_1) (and (and (>= y_4_1 0) (<= y_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))) (and (not expr_10_1) (= error_1 3))) (block_34_constructor_18_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (block_34_constructor_18_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (summary_7_constructor_18_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_32__17_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (= x_2_2 expr_15_1) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 expr_14_0) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 x_2_1) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 y_4_1) (and (= error_1 error_0) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_2_1) (and (and (>= y_4_1 0) (<= y_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))))))))) true) (block_33_return_constructor_18_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_2 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_33_return_constructor_18_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) true) true) (summary_7_constructor_18_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(declare-fun |contract_initializer_35_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_36_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= y_4_1 y_4_0))) (contract_initializer_entry_36_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(declare-fun |contract_initializer_after_init_37_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_entry_36_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) true) true) (contract_initializer_after_init_37_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_after_init_37_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (summary_7_constructor_18_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_1 state_2 x_2_2 y_4_2) true)) (> error_1 0)) (contract_initializer_35_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_after_init_37_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (= error_1 0) (and (summary_7_constructor_18_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_1 state_2 x_2_2 y_4_2) true))) true) (contract_initializer_35_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_2))))


(declare-fun |implicit_constructor_entry_38_B_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_2_2 x_2_0))) true) (and true (= x_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_38_B_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (implicit_constructor_entry_38_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (contract_initializer_35_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_2 state_2 x_2_2 y_4_3) (and (= y_4_2 expr_24_0) (and (=> true true) (and (= expr_24_0 2) true))))) (> error_1 0)) (summary_constructor_6_B_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (implicit_constructor_entry_38_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (contract_initializer_28_B_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_2_2 state_3 x_2_3) (and (= error_1 0) (and (contract_initializer_35_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_2 state_2 x_2_2 y_4_3) (and (= y_4_2 expr_24_0) (and (=> true true) (and (= expr_24_0 2) true))))))) (> error_2 0)) (summary_constructor_6_B_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (implicit_constructor_entry_38_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_2 0) (and (contract_initializer_28_B_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_2_2 state_3 x_2_3) (and (= error_1 0) (and (contract_initializer_35_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_2 state_2 x_2_2 y_4_3) (and (= y_4_2 expr_24_0) (and (=> true true) (and (= expr_24_0 2) true)))))))) true) (summary_constructor_6_B_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (summary_constructor_6_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_4_B_35_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_39_function_f__47_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_40_f_46_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(block_39_function_f__47_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_39_function_f__47_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_40_f_46_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_41_return_function_f__47_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_42_function_f__47_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_40_f_46_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_43_1 (= expr_41_0 expr_42_0)) (and (=> true true) (and (= expr_42_0 2) (and (=> true (and (>= expr_41_0 0) (<= expr_41_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_41_0 x_2_1) true)))))) (and (not expr_43_1) (= error_1 4))) (block_42_function_f__47_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (block_42_function_f__47_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_14_function_f__47_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_40_f_46_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 error_0) (and (= expr_43_1 (= expr_41_0 expr_42_0)) (and (=> true true) (and (= expr_42_0 2) (and (=> true (and (>= expr_41_0 0) (<= expr_41_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_41_0 x_2_1) true))))))) true) (block_41_return_function_f__47_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_41_return_function_f__47_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_14_function_f__47_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_43_function_f__47_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(block_43_function_f__47_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_43_function_f__47_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_14_function_f__47_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_5_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_5_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_5_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_5_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_15_function_f__47_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (interface_9_C_48_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_15_function_f__47_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_9_C_48_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |contract_initializer_44_C_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_45_C_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_45_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_46_C_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_entry_45_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_46_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_after_init_46_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_44_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |block_47_constructor_34_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_48__33_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(block_47_constructor_34_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_47_constructor_34_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_48__33_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_49_return_constructor_34_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_50_constructor_34_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_48__33_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_30_1 (= expr_28_0 expr_29_0)) (and (=> true true) (and (= expr_29_0 2) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_0 x_2_1) true)))))) (and (not expr_30_1) (= error_1 6))) (block_50_constructor_34_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (block_50_constructor_34_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_13_constructor_34_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_48__33_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 error_0) (and (= expr_30_1 (= expr_28_0 expr_29_0)) (and (=> true true) (and (= expr_29_0 2) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_0 x_2_1) true))))))) true) (block_49_return_constructor_34_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_49_return_constructor_34_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_13_constructor_34_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_51_B_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_52_B_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) (contract_initializer_entry_52_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |contract_initializer_after_init_53_B_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_entry_52_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (contract_initializer_after_init_53_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_after_init_53_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_13_constructor_34_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true)) (> error_1 0)) (contract_initializer_51_B_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_after_init_53_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 0) (and (summary_13_constructor_34_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2) true))) true) (contract_initializer_51_B_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_54_constructor_18_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_55__17_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(block_54_constructor_18_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_54_constructor_18_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= y_4_1 y_4_0))) true)) true) (block_55__17_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(declare-fun |block_56_return_constructor_18_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_57_constructor_18_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_55__17_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_2_1) (and (and (>= y_4_1 0) (<= y_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))) (and (not expr_10_1) (= error_1 7))) (block_57_constructor_18_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (block_57_constructor_18_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (summary_12_constructor_18_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_55__17_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (= x_2_2 expr_15_1) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 expr_14_0) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 x_2_1) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 y_4_1) (and (= error_1 error_0) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_2_1) (and (and (>= y_4_1 0) (<= y_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))))))))) true) (block_56_return_constructor_18_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_2 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (block_56_return_constructor_18_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) true) true) (summary_12_constructor_18_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(declare-fun |contract_initializer_58_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_59_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= y_4_1 y_4_0))) (contract_initializer_entry_59_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(declare-fun |contract_initializer_after_init_60_A_19_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_entry_59_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) true) true) (contract_initializer_after_init_60_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_after_init_60_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (summary_12_constructor_18_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_1 state_2 x_2_2 y_4_2) true)) (> error_1 0)) (contract_initializer_58_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (contract_initializer_after_init_60_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (= error_1 0) (and (summary_12_constructor_18_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_1 state_2 x_2_2 y_4_2) true))) true) (contract_initializer_58_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_2))))


(declare-fun |implicit_constructor_entry_61_C_48_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_2_2 x_2_0))) (and true (= x_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_61_C_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (implicit_constructor_entry_61_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_58_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_2 state_2 x_2_2 y_4_3) (and (= y_4_2 expr_24_0) (and (=> true true) (and (= expr_24_0 2) true))))) (> error_1 0)) (summary_constructor_11_C_48_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (implicit_constructor_entry_61_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_51_B_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_2_2 state_3 x_2_3) (and (= error_1 0) (and (contract_initializer_58_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_2 state_2 x_2_2 y_4_3) (and (= y_4_2 expr_24_0) (and (=> true true) (and (= expr_24_0 2) true))))))) (> error_2 0)) (summary_constructor_11_C_48_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 x_2_0 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (implicit_constructor_entry_61_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_44_C_48_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 x_2_3 x_2_4) (and (= error_2 0) (and (contract_initializer_51_B_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_2_2 state_3 x_2_3) (and (= error_1 0) (and (contract_initializer_58_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_2 state_2 x_2_2 y_4_3) (and (= y_4_2 expr_24_0) (and (=> true true) (and (= expr_24_0 2) true))))))))) (> error_3 0)) (summary_constructor_11_C_48_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 x_2_0 x_2_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (implicit_constructor_entry_61_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_3 0) (and (contract_initializer_44_C_48_0 error_3 this_0 abi_0 crypto_0 tx_0 state_3 state_4 x_2_3 x_2_4) (and (= error_2 0) (and (contract_initializer_51_B_35_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_2_2 state_3 x_2_3) (and (= error_1 0) (and (contract_initializer_58_A_19_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_2 state_2 x_2_2 y_4_3) (and (= y_4_2 expr_24_0) (and (=> true true) (and (= expr_24_0 2) true)))))))))) true) (summary_constructor_11_C_48_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_4 x_2_0 x_2_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (summary_constructor_11_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_9_C_48_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |error_target_8_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (summary_constructor_2_A_19_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_8_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (summary_constructor_6_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_8_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (summary_constructor_11_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_8_0)))


(declare-fun |error_target_9_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (summary_constructor_6_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 2))) error_target_9_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (summary_constructor_11_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 2))) error_target_9_0)))


(declare-fun |error_target_10_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (summary_constructor_6_B_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 3))) error_target_10_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> (and (and (summary_constructor_11_C_48_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 3))) error_target_10_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_24_0 Int) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_41_0 Int) (expr_42_0 Int) (expr_43_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (state_4 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (x_2_4 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int) (y_4_5 Int))
(=> error_target_10_0 false)))
(check-sat)