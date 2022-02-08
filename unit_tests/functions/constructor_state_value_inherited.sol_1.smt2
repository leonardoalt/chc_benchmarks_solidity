(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_B_4_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_B_4_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_B_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_1_B_4_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |interface_3_C_33_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_4_C_33_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_5_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int))
(=> (= error_0 0) (nondet_interface_4_C_33_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_0 x_3_0))))


(declare-fun |summary_6_constructor_20_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_7_function_f__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_8_function_f__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_22_0 Int) (y_22_1 Int))
(=> (and (and (nondet_interface_4_C_33_0 error_0 this_0 abi_0 crypto_0 state_0 x_3_0 state_1 x_3_1) true) (and (= error_0 0) (summary_8_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 y_22_0 state_2 x_3_2 y_22_1))) (nondet_interface_4_C_33_0 error_1 this_0 abi_0 crypto_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |contract_initializer_9_B_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_10_B_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_22_0 Int) (y_22_1 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_0 x_3_0))) (contract_initializer_entry_10_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_0))))


(declare-fun |contract_initializer_after_init_11_B_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_22_0 Int) (y_22_1 Int))
(=> (and (and (contract_initializer_entry_10_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 5) true)))) true) (contract_initializer_after_init_11_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_22_0 Int) (y_22_1 Int))
(=> (and (and (contract_initializer_after_init_11_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_9_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_12_B_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_22_0 Int) (y_22_1 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_12_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_22_0 Int) (y_22_1 Int))
(=> (and (and (implicit_constructor_entry_12_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (contract_initializer_9_B_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_2_B_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_22_0 Int) (y_22_1 Int))
(=> (and (and (implicit_constructor_entry_12_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= error_1 0) (and (contract_initializer_9_B_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))) true) (summary_constructor_2_B_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (y_22_0 Int) (y_22_1 Int))
(=> (and (and (summary_constructor_2_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_B_4_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_13_function_f__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_14_f_31_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(block_13_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (block_13_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= y_22_1 y_22_0))) true)) true) (block_14_f_31_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1))))


(declare-fun |block_15_return_function_f__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_16_function_f__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (block_14_f_31_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1) (and (= expr_28_1 (= expr_26_0 expr_27_0)) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_3_1) (and (=> true (and (>= expr_26_0 0) (<= expr_26_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_0 y_22_1) (and (and (>= y_22_1 0) (<= y_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))) (and (not expr_28_1) (= error_1 1))) (block_16_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (block_16_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1) (summary_7_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (block_14_f_31_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1) (and (= error_1 error_0) (and (= expr_28_1 (= expr_26_0 expr_27_0)) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_3_1) (and (=> true (and (>= expr_26_0 0) (<= expr_26_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_0 y_22_1) (and (and (>= y_22_1 0) (<= y_22_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))) true) (block_15_return_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (block_15_return_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1) true) true) (summary_7_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1))))


(declare-fun |block_17_function_f__32_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(block_17_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (block_17_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1) (and (summary_7_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_3_1 y_22_1 state_3 x_3_2 y_22_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3017696395)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 179)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 222)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 100)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 139)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) (and true (= y_22_1 y_22_0))) true))))))) true) (summary_8_function_f__32_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_3 x_3_2 y_22_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (interface_3_C_33_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_8_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1) (= error_0 0))) (interface_3_C_33_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |block_18_constructor_20_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_19__19_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(block_18_constructor_20_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (block_18_constructor_20_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) true)) true) (block_19__19_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |block_20_return_constructor_20_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_21_constructor_20_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (block_19__19_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= expr_12_1 (= expr_10_0 expr_11_0)) (and (=> true true) (and (= expr_11_0 5) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_10_0 x_3_1) true)))))) (and (not expr_12_1) (= error_1 3))) (block_21_constructor_20_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (block_21_constructor_20_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (summary_6_constructor_20_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (block_19__19_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= x_3_2 expr_17_1) (and (=> true (and (>= expr_17_1 0) (<= expr_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_17_1 expr_16_0) (and (=> true (and (>= expr_15_0 0) (<= expr_15_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_0 x_3_1) (and (=> true true) (and (= expr_16_0 10) (and (= error_1 error_0) (and (= expr_12_1 (= expr_10_0 expr_11_0)) (and (=> true true) (and (= expr_11_0 5) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_10_0 x_3_1) true)))))))))))))) true) (block_20_return_constructor_20_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (block_20_return_constructor_20_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (summary_6_constructor_20_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_22_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_23_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (contract_initializer_entry_23_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(declare-fun |contract_initializer_after_init_24_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (contract_initializer_entry_23_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) true) (contract_initializer_after_init_24_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (contract_initializer_after_init_24_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (summary_6_constructor_20_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true)) (> error_1 0)) (contract_initializer_22_C_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (contract_initializer_after_init_24_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_1 0) (and (summary_6_constructor_20_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_3_1 state_2 x_3_2) true))) true) (contract_initializer_22_C_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(declare-fun |contract_initializer_25_B_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_26_B_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_3_2 x_3_0))) (contract_initializer_entry_26_B_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_3_0 x_3_2))))


(declare-fun |contract_initializer_after_init_27_B_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (contract_initializer_entry_26_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) (and (= x_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 5) true)))) true) (contract_initializer_after_init_27_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (contract_initializer_after_init_27_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1) true) true) (contract_initializer_25_B_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_3_0 x_3_1))))


(declare-fun |implicit_constructor_entry_28_C_33_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_3_1 x_3_0))) true) (and true (= x_3_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_28_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (implicit_constructor_entry_28_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_25_B_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)) (> error_1 0)) (summary_constructor_5_C_33_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_2 x_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (implicit_constructor_entry_28_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (contract_initializer_22_C_33_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_25_B_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true)))) (> error_2 0)) (summary_constructor_5_C_33_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (implicit_constructor_entry_28_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) (and (= error_2 0) (and (contract_initializer_22_C_33_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 x_3_2 state_3 x_3_3) (and (= error_1 0) (and (contract_initializer_25_B_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_3_1 x_3_2) true))))) true) (summary_constructor_5_C_33_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_3 x_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (summary_constructor_5_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_3_C_33_0 this_0 abi_0 crypto_0 state_1 x_3_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (interface_3_C_33_0 this_0 abi_0 crypto_0 state_0 x_3_0) true) (and (summary_8_function_f__32_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 y_22_0 state_1 x_3_1 y_22_1) (= error_0 1))) error_target_4_0)))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> (and (and (summary_constructor_5_C_33_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_3_0 state_1 x_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 3))) error_target_5_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Bool) (expr_15_0 Int) (expr_16_0 Int) (expr_17_1 Int) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_2_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_3_0 Int) (x_3_1 Int) (x_3_2 Int) (x_3_3 Int) (y_22_0 Int) (y_22_1 Int) (y_22_2 Int) (y_22_3 Int))
(=> error_target_5_0 false)))
(check-sat)