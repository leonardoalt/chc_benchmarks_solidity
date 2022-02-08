(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_83_0| (Int |abi_type| |crypto_type| |state_type| Bool ) Bool)
(declare-fun |nondet_interface_1_C_83_0| (Int Int |abi_type| |crypto_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |summary_constructor_2_C_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool))
(=> (= error_0 0) (nondet_interface_1_C_83_0 error_0 this_0 abi_0 crypto_0 state_0 x_57_0 state_0 x_57_0))))


(declare-fun |summary_3_function_f__33_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |summary_4_function_f__33_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (nondet_interface_1_C_83_0 error_0 this_0 abi_0 crypto_0 state_0 x_57_0 state_1 x_57_1) true) (and (= error_0 0) (summary_4_function_f__33_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_57_1 state_2 x_57_2))) (nondet_interface_1_C_83_0 error_1 this_0 abi_0 crypto_0 state_0 x_57_0 state_2 x_57_2))))


(declare-fun |summary_5_function_g_data__43_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |summary_6_function_g__54_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |summary_7_function_g__54_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (nondet_interface_1_C_83_0 error_1 this_0 abi_0 crypto_0 state_0 x_57_0 state_1 x_57_1) true) (and (= error_1 0) (summary_7_function_g__54_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_57_1 state_2 x_57_2))) (nondet_interface_1_C_83_0 error_2 this_0 abi_0 crypto_0 state_0 x_57_0 state_2 x_57_2))))


(declare-fun |summary_8_function_h_data__67_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |summary_9_function_h__82_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |summary_10_function_h__82_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (nondet_interface_1_C_83_0 error_2 this_0 abi_0 crypto_0 state_0 x_57_0 state_1 x_57_1) true) (and (= error_2 0) (summary_10_function_h__82_83_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 x_57_1 state_2 x_57_2))) (nondet_interface_1_C_83_0 error_3 this_0 abi_0 crypto_0 state_0 x_57_0 state_2 x_57_2))))


(declare-fun |block_11_function_f__33_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |block_12_f_32_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(block_11_function_f__33_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1)))


(assert
(forall ( (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_11_function_f__33_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_57_1 x_57_0))) true) true)) true) (block_12_f_32_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1))))


(declare-fun |block_13_return_function_f__33_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_12_f_32_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (=> true (and (>= expr_29_1 0) (<= expr_29_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_1 (|msg.value| tx_0)) (and (=> true (and (>= expr_27_1 0) (<= expr_27_1 1461501637330902918203684832716283019655932542975))) (and (= expr_27_1 (|msg.sender| tx_0)) (and (=> true true) (and (= expr_22_0 567) (and (=> true true) (and (= expr_21_0 134) true))))))))) true) (block_13_return_function_f__33_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1))))


(assert
(forall ( (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_13_return_function_f__33_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) true) true) (summary_3_function_f__33_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1))))


(declare-fun |block_14_function_f__33_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(block_14_function_f__33_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1)))


(assert
(forall ( (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_14_function_f__33_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (summary_3_function_f__33_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_57_1 state_3 x_57_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and true (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_57_1 x_57_0))) true) true))))))) true) (summary_4_function_f__33_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_3 x_57_2))))


(assert
(forall ( (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (interface_0_C_83_0 this_0 abi_0 crypto_0 state_0 x_57_0) true) (and (summary_4_function_f__33_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (= error_0 0))) (interface_0_C_83_0 this_0 abi_0 crypto_0 state_1 x_57_1))))


(declare-fun |block_15_function_g_data__43_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_16_g_data_42_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(block_15_function_g_data__43_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_1)))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_15_function_g_data__43_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_57_1 x_57_0))) true) true)) true) (block_16_g_data_42_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_1))))


(declare-fun |block_17_return_function_g_data__43_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_18_function_g_data__43_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_16_g_data_42_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_1) (and (= expr_39_0 true) (and (= _36_1 0) true))) (and (not expr_39_0) (= error_1 1))) (block_18_function_g_data__43_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_1))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (block_18_function_g_data__43_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_1) (summary_5_function_g_data__43_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_1))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_16_g_data_42_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_1) (and (= error_1 error_0) (and (= expr_39_0 true) (and (= _36_1 0) true)))) true) (block_17_return_function_g_data__43_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_1))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_17_return_function_g_data__43_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_1) true) true) (summary_5_function_g_data__43_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_1))))


(declare-fun |block_19_function_g__54_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |block_20_g_53_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(block_19_function_g__54_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1)))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_19_function_g__54_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_57_1 x_57_0))) true) true)) true) (block_20_g_53_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1))))


(declare-fun |block_21_return_function_g__54_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |summary_22_function_g_data__43_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (summary_5_function_g_data__43_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_2) (summary_22_function_g_data__43_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_2))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_20_g_53_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (summary_22_function_g_data__43_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_57_1 state_1 x_57_1 _36_2) (and true true))) (> error_1 0)) (summary_6_function_g__54_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1))))


(declare-fun |summary_23_function_g_data__43_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (summary_5_function_g_data__43_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_3) (summary_23_function_g_data__43_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _36_3))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_20_g_53_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (summary_23_function_g_data__43_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_57_1 state_1 x_57_1 _36_3) (and (=> true (and (>= expr_48_0 0) (<= expr_48_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_48_0 _36_2) (and (= error_1 0) (and (summary_22_function_g_data__43_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_57_1 state_1 x_57_1 _36_2) (and true true))))))) (> error_2 0)) (summary_6_function_g__54_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_20_g_53_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (=> true (and (>= expr_50_0 0) (<= expr_50_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_0 _36_3) (and (= error_2 0) (and (summary_23_function_g_data__43_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_57_1 state_1 x_57_1 _36_3) (and (=> true (and (>= expr_48_0 0) (<= expr_48_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_48_0 _36_2) (and (= error_1 0) (and (summary_22_function_g_data__43_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_57_1 state_1 x_57_1 _36_2) (and true true)))))))))) true) (block_21_return_function_g__54_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_21_return_function_g__54_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) true) true) (summary_6_function_g__54_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1))))


(declare-fun |block_24_function_g__54_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(block_24_function_g__54_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1)))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_24_function_g__54_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (summary_6_function_g__54_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_57_1 state_3 x_57_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_57_1 x_57_0))) true) true))))))) true) (summary_7_function_g__54_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_3 x_57_2))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (interface_0_C_83_0 this_0 abi_0 crypto_0 state_0 x_57_0) true) (and (summary_7_function_g__54_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (= error_0 0))) (interface_0_C_83_0 this_0 abi_0 crypto_0 state_1 x_57_1))))


(declare-fun |block_25_function_h_data__67_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_26_h_data_66_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(block_25_function_h_data__67_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _60_1)))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_25_function_h_data__67_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _60_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_57_1 x_57_0))) true) true)) true) (block_26_h_data_66_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _60_1))))


(declare-fun |block_27_return_function_h_data__67_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_28_function_h_data__67_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_26_h_data_66_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _60_1) (and (= expr_63_0 x_57_1) (and (= _60_1 0) true))) (and (not expr_63_0) (= error_1 3))) (block_28_function_h_data__67_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _60_1))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (block_28_function_h_data__67_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _60_1) (summary_8_function_h_data__67_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _60_1))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_26_h_data_66_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _60_1) (and (= error_1 error_0) (and (= expr_63_0 x_57_1) (and (= _60_1 0) true)))) true) (block_27_return_function_h_data__67_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _60_1))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_27_return_function_h_data__67_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _60_1) true) true) (summary_8_function_h_data__67_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1 _60_1))))


(declare-fun |block_29_function_h__82_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |block_30_h_81_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(block_29_function_h__82_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1)))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_29_function_h__82_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_57_1 x_57_0))) true) true)) true) (block_30_h_81_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1))))


(declare-fun |block_31_return_function_h__82_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |summary_32_function_h_data__67_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (summary_8_function_h_data__67_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_2 _60_2) (summary_32_function_h_data__67_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_2 _60_2))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_30_h_81_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (summary_32_function_h_data__67_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_57_2 state_1 x_57_2 _60_2) (and true (and (= x_57_2 expr_72_1) (and (= expr_72_1 expr_71_0) (and (= expr_70_0 x_57_1) (and (= expr_71_0 false) true))))))) (> error_1 0)) (summary_9_function_h__82_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_2))))


(declare-fun |summary_33_function_h_data__67_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (summary_8_function_h_data__67_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_2 _60_3) (summary_33_function_h_data__67_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_2 _60_3))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_30_h_81_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (summary_33_function_h_data__67_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_57_2 state_1 x_57_2 _60_3) (and (=> true (and (>= expr_76_0 0) (<= expr_76_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_76_0 _60_2) (and (= error_1 0) (and (summary_32_function_h_data__67_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_57_2 state_1 x_57_2 _60_2) (and true (and (= x_57_2 expr_72_1) (and (= expr_72_1 expr_71_0) (and (= expr_70_0 x_57_1) (and (= expr_71_0 false) true))))))))))) (> error_2 0)) (summary_9_function_h__82_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_2))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_30_h_81_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (=> true (and (>= expr_78_0 0) (<= expr_78_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_78_0 _60_3) (and (= error_2 0) (and (summary_33_function_h_data__67_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_57_2 state_1 x_57_2 _60_3) (and (=> true (and (>= expr_76_0 0) (<= expr_76_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_76_0 _60_2) (and (= error_1 0) (and (summary_32_function_h_data__67_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_57_2 state_1 x_57_2 _60_2) (and true (and (= x_57_2 expr_72_1) (and (= expr_72_1 expr_71_0) (and (= expr_70_0 x_57_1) (and (= expr_71_0 false) true)))))))))))))) true) (block_31_return_function_h__82_83_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_2))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_31_return_function_h__82_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) true) true) (summary_9_function_h__82_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1))))


(declare-fun |block_34_function_h__82_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(block_34_function_h__82_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1)))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (block_34_function_h__82_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (and (summary_9_function_h__82_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_57_1 state_3 x_57_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_4_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_4_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_4_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_4_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3100234597)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 184)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 201)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 211)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 101)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_57_1 x_57_0))) true) true))))))) true) (summary_10_function_h__82_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_3 x_57_2))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (interface_0_C_83_0 this_0 abi_0 crypto_0 state_0 x_57_0) true) (and (summary_10_function_h__82_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (= error_0 0))) (interface_0_C_83_0 this_0 abi_0 crypto_0 state_1 x_57_1))))


(declare-fun |contract_initializer_35_C_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool Bool ) Bool)
(declare-fun |contract_initializer_entry_36_C_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool Bool ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_57_1 x_57_0))) (contract_initializer_entry_36_C_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_57_0 x_57_1))))


(declare-fun |contract_initializer_after_init_37_C_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool Bool ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_56_0 Bool) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (contract_initializer_entry_36_C_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_57_0 x_57_1) (and (= x_57_2 expr_56_0) (and (= expr_56_0 true) true))) true) (contract_initializer_after_init_37_C_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_57_0 x_57_2))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_56_0 Bool) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (contract_initializer_after_init_37_C_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_57_0 x_57_1) true) true) (contract_initializer_35_C_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_57_0 x_57_1))))


(declare-fun |implicit_constructor_entry_38_C_83_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool Bool ) Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_56_0 Bool) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_57_1 x_57_0))) (and true (= x_57_1 false))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_38_C_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_57_0 x_57_1))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_56_0 Bool) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (implicit_constructor_entry_38_C_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_57_0 x_57_1) (and (contract_initializer_35_C_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_57_1 x_57_2) true)) (> error_1 0)) (summary_constructor_2_C_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_57_0 x_57_2))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_56_0 Bool) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (implicit_constructor_entry_38_C_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_57_0 x_57_1) (and (= error_1 0) (and (contract_initializer_35_C_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_57_1 x_57_2) true))) true) (summary_constructor_2_C_83_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_57_0 x_57_2))))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_56_0 Bool) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (summary_constructor_2_C_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_57_0 x_57_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_83_0 this_0 abi_0 crypto_0 state_1 x_57_1))))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_36_4 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (_60_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_56_0 Bool) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (interface_0_C_83_0 this_0 abi_0 crypto_0 state_0 x_57_0) true) (and (summary_7_function_g__54_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (= error_0 1))) error_target_5_0)))


(declare-fun |error_target_6_0| () Bool)
(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_36_4 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (_60_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_56_0 Bool) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> (and (and (interface_0_C_83_0 this_0 abi_0 crypto_0 state_0 x_57_0) true) (and (summary_10_function_h__82_83_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_57_0 state_1 x_57_1) (= error_0 3))) error_target_6_0)))


(assert
(forall ( (_36_0 Int) (_36_1 Int) (_36_2 Int) (_36_3 Int) (_36_4 Int) (_60_0 Int) (_60_1 Int) (_60_2 Int) (_60_3 Int) (_60_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_21_0 Int) (expr_22_0 Int) (expr_27_1 Int) (expr_29_1 Int) (expr_39_0 Bool) (expr_48_0 Int) (expr_50_0 Int) (expr_56_0 Bool) (expr_63_0 Bool) (expr_70_0 Bool) (expr_71_0 Bool) (expr_72_1 Bool) (expr_76_0 Int) (expr_78_0 Int) (funds_0_0 Int) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_uint256_$_abstract_0 Int) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_57_0 Bool) (x_57_1 Bool) (x_57_2 Bool))
(=> error_target_6_0 false)))
(check-sat)