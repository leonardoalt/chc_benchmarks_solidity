(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_49_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_49_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int))
(=> (= error_0 0) (nondet_interface_1_C_49_0 error_0 this_0 abi_0 crypto_0 state_0 x_4_0 state_0 x_4_0))))


(declare-fun |summary_3_function_g__16_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |summary_4_constructor_32_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_5_function_f__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_6_function_f__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (nondet_interface_1_C_49_0 error_0 this_0 abi_0 crypto_0 state_0 x_4_0 state_1 x_4_1) true) (and (= error_0 0) (summary_6_function_f__48_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2))) (nondet_interface_1_C_49_0 error_1 this_0 abi_0 crypto_0 state_0 x_4_0 state_2 x_4_2))))


(declare-fun |block_7_function_g__16_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(declare-fun |block_8_g_15_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(block_7_function_g__16_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1 _7_1)))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_7_function_g__16_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1 _7_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) true)) true) (block_8_g_15_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1 _7_1))))


(declare-fun |block_9_return_function_g__16_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_8_g_15_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1 _7_1) (and (= _7_2 expr_13_1) (and (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_1 (select (|balances| state_1) expr_12_1)) (and (=> true (and (>= expr_12_1 0) (<= expr_12_1 1461501637330902918203684832716283019655932542975))) (and (= expr_12_1 expr_11_0) (and (=> true true) (and (= expr_11_0 this_0) (and (= _7_1 0) true)))))))))) true) (block_9_return_function_g__16_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1 _7_2))))


(declare-fun |block_10_return_ghost_g_14_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_10_return_ghost_g_14_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1 _7_2) (and (= _7_2 expr_13_1) (and (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_13_1 0) (<= expr_13_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_1 (select (|balances| state_1) expr_12_1)) (and (=> true (and (>= expr_12_1 0) (<= expr_12_1 1461501637330902918203684832716283019655932542975))) (and (= expr_12_1 expr_11_0) (and (=> true true) (and (= expr_11_0 this_0) (and (= _7_1 0) true)))))))))) true) (block_9_return_function_g__16_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1 _7_2))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_9_return_function_g__16_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1 _7_1) true) true) (summary_3_function_g__16_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1 _7_1))))


(declare-fun |block_11_function_f__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_12_f_47_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(block_11_function_f__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1)))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_11_function_f__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) true)) true) (block_12_f_47_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |block_13_return_function_f__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_14_function_f__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_12_f_47_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= expr_38_1 (= expr_36_0 expr_37_0)) (and (=> true true) (and (= expr_37_0 0) (and (=> true (and (>= expr_36_0 0) (<= expr_36_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_36_0 x_4_1) true)))))) (and (not expr_38_1) (= error_1 1))) (block_14_function_f__48_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (block_14_function_f__48_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (summary_5_function_f__48_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |block_15_function_f__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_12_f_47_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= expr_44_1 (> expr_42_0 expr_43_0)) (and (=> true true) (and (= expr_43_0 0) (and (=> true (and (>= expr_42_0 0) (<= expr_42_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_42_0 x_4_1) (and (= error_1 error_0) (and (= expr_38_1 (= expr_36_0 expr_37_0)) (and (=> true true) (and (= expr_37_0 0) (and (=> true (and (>= expr_36_0 0) (<= expr_36_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_36_0 x_4_1) true)))))))))))) (and (not expr_44_1) (= error_2 2))) (block_15_function_f__48_49_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (block_15_function_f__48_49_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (summary_5_function_f__48_49_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_12_f_47_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_2 error_1) (and (= expr_44_1 (> expr_42_0 expr_43_0)) (and (=> true true) (and (= expr_43_0 0) (and (=> true (and (>= expr_42_0 0) (<= expr_42_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_42_0 x_4_1) (and (= error_1 error_0) (and (= expr_38_1 (= expr_36_0 expr_37_0)) (and (=> true true) (and (= expr_37_0 0) (and (=> true (and (>= expr_36_0 0) (<= expr_36_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_36_0 x_4_1) true))))))))))))) true) (block_13_return_function_f__48_49_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_13_return_function_f__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) true) (summary_5_function_f__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |block_16_function_f__48_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(block_16_function_f__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1)))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_16_function_f__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (summary_5_function_f__48_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_4_1 state_3 x_4_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) true))))))) true) (summary_6_function_f__48_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_3 x_4_2))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (interface_0_C_49_0 this_0 abi_0 crypto_0 state_0 x_4_0) true) (and (summary_6_function_f__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (= error_0 0))) (interface_0_C_49_0 this_0 abi_0 crypto_0 state_1 x_4_1))))


(declare-fun |block_17_constructor_32_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_18__31_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(block_17_constructor_32_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1)))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_17_constructor_32_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) true)) true) (block_18__31_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |block_19_return_constructor_32_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_20_constructor_32_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_18__31_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= expr_22_1 (= expr_20_0 expr_21_0)) (and (=> true true) (and (= expr_21_0 0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 x_4_1) true)))))) (and (not expr_22_1) (= error_1 4))) (block_20_constructor_32_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (block_20_constructor_32_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (summary_4_constructor_32_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |block_21_constructor_32_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_18__31_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= expr_28_1 (> expr_26_0 expr_27_0)) (and (=> true true) (and (= expr_27_0 0) (and (=> true (and (>= expr_26_0 0) (<= expr_26_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_0 x_4_1) (and (= error_1 error_0) (and (= expr_22_1 (= expr_20_0 expr_21_0)) (and (=> true true) (and (= expr_21_0 0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 x_4_1) true)))))))))))) (and (not expr_28_1) (= error_2 5))) (block_21_constructor_32_49_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (block_21_constructor_32_49_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (summary_4_constructor_32_49_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_18__31_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_2 error_1) (and (= expr_28_1 (> expr_26_0 expr_27_0)) (and (=> true true) (and (= expr_27_0 0) (and (=> true (and (>= expr_26_0 0) (<= expr_26_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_0 x_4_1) (and (= error_1 error_0) (and (= expr_22_1 (= expr_20_0 expr_21_0)) (and (=> true true) (and (= expr_21_0 0) (and (=> true (and (>= expr_20_0 0) (<= expr_20_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_0 x_4_1) true))))))))))))) true) (block_19_return_constructor_32_49_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (block_19_return_constructor_32_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) true) (summary_4_constructor_32_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |contract_initializer_22_C_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_23_C_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_4_1 x_4_0))) true) (contract_initializer_entry_23_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |summary_24_function_g__16_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (summary_3_function_g__16_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1 _7_2) (summary_24_function_g__16_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1 _7_2))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_entry_23_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (summary_24_function_g__16_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_1 x_4_1 _7_2) (and true true))) (> error_1 0)) (contract_initializer_22_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1))))


(declare-fun |contract_initializer_after_init_25_C_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_3_0 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_entry_23_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= x_4_2 expr_3_0) (and (=> true (and (>= expr_3_0 0) (<= expr_3_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_3_0 _7_2) (and (= error_1 0) (and (summary_24_function_g__16_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_1 x_4_1 _7_2) (and true true))))))) true) (contract_initializer_after_init_25_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_2))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_3_0 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_25_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (summary_4_constructor_32_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)) (> error_1 0)) (contract_initializer_22_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_3_0 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (contract_initializer_after_init_25_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 0) (and (summary_4_constructor_32_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true))) true) (contract_initializer_22_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(declare-fun |implicit_constructor_entry_26_C_49_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_3_0 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_4_2 x_4_0))) true) (and true (= x_4_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_26_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_3_0 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (implicit_constructor_entry_26_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (contract_initializer_22_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true)) (> error_1 0)) (summary_constructor_2_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_3_0 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (implicit_constructor_entry_26_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (and (= error_1 0) (and (contract_initializer_22_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_4_1 state_2 x_4_2) true))) true) (summary_constructor_2_C_49_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_2 x_4_2))))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_3_0 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (summary_constructor_2_C_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_49_0 this_0 abi_0 crypto_0 state_1 x_4_1))))


(declare-fun |error_target_6_0| () Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_3_0 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (interface_0_C_49_0 this_0 abi_0 crypto_0 state_0 x_4_0) true) (and (summary_6_function_f__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (= error_0 1))) error_target_6_0)))


(declare-fun |error_target_7_0| () Bool)
(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_3_0 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> (and (and (interface_0_C_49_0 this_0 abi_0 crypto_0 state_0 x_4_0) true) (and (summary_6_function_f__48_49_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_4_0 state_1 x_4_1) (= error_0 2))) error_target_7_0)))


(assert
(forall ( (_7_0 Int) (_7_1 Int) (_7_2 Int) (_7_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_13_1 Int) (expr_20_0 Int) (expr_21_0 Int) (expr_22_1 Bool) (expr_26_0 Int) (expr_27_0 Int) (expr_28_1 Bool) (expr_36_0 Int) (expr_37_0 Int) (expr_38_1 Bool) (expr_3_0 Int) (expr_42_0 Int) (expr_43_0 Int) (expr_44_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_view$__$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_4_0 Int) (x_4_1 Int) (x_4_2 Int))
(=> error_target_7_0 false)))
(check-sat)