(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_38_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_38_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int))
(=> (= error_0 0) (nondet_interface_1_C_38_0 error_0 this_0 abi_0 crypto_0 state_0 x_5_0 state_0 x_5_0))))


(declare-fun |summary_3_constructor_15_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_4_function_f__37_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_5_function_f__37_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_6_f_36_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(block_5_function_f__37_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1)))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (and (and (block_5_function_f__37_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_5_1 x_5_0))) (and true (= y_17_1 y_17_0))) true)) true) (block_6_f_36_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1))))


(declare-fun |block_7_return_function_f__37_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_8_function_f__37_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (and (and (block_6_f_36_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1) (and (= expr_25_1 (> expr_23_0 expr_24_0)) (and (=> true true) (and (= expr_24_0 0) (and (=> true (and (>= expr_23_0 0) (<= expr_23_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_0 y_17_1) (and (= _20_1 0) (and (and (>= y_17_1 0) (<= y_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))) (and (not expr_25_1) (= error_1 1))) (block_8_function_f__37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (block_8_function_f__37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1) (summary_4_function_f__37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1))))


(declare-fun |block_9_function_f__37_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (and (and (block_6_f_36_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1) (and (= expr_31_1 (= expr_29_0 expr_30_0)) (and (=> true true) (and (= expr_30_0 0) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 x_5_1) (and (= error_1 error_0) (and (= expr_25_1 (> expr_23_0 expr_24_0)) (and (=> true true) (and (= expr_24_0 0) (and (=> true (and (>= expr_23_0 0) (<= expr_23_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_0 y_17_1) (and (= _20_1 0) (and (and (>= y_17_1 0) (<= y_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))))) (and (not expr_31_1) (= error_2 2))) (block_9_function_f__37_38_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (block_9_function_f__37_38_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1) (summary_4_function_f__37_38_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (and (and (block_6_f_36_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1) (and (= _20_2 expr_34_0) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 y_17_1) (and (= error_2 error_1) (and (= expr_31_1 (= expr_29_0 expr_30_0)) (and (=> true true) (and (= expr_30_0 0) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 x_5_1) (and (= error_1 error_0) (and (= expr_25_1 (> expr_23_0 expr_24_0)) (and (=> true true) (and (= expr_24_0 0) (and (=> true (and (>= expr_23_0 0) (<= expr_23_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_0 y_17_1) (and (= _20_1 0) (and (and (>= y_17_1 0) (<= y_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))))))))) true) (block_7_return_function_f__37_38_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_2))))


(declare-fun |block_10_return_ghost_f_35_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (and (and (block_10_return_ghost_f_35_38_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_2) (and (= _20_2 expr_34_0) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 y_17_1) (and (= error_2 error_1) (and (= expr_31_1 (= expr_29_0 expr_30_0)) (and (=> true true) (and (= expr_30_0 0) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 x_5_1) (and (= error_1 error_0) (and (= expr_25_1 (> expr_23_0 expr_24_0)) (and (=> true true) (and (= expr_24_0 0) (and (=> true (and (>= expr_23_0 0) (<= expr_23_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_0 y_17_1) (and (= _20_1 0) (and (and (>= y_17_1 0) (<= y_17_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))))))))) true) (block_7_return_function_f__37_38_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_2))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (and (and (block_7_return_function_f__37_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1) true) true) (summary_4_function_f__37_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_1 _20_1))))


(declare-fun |block_11_constructor_15_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_12__14_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(block_11_constructor_15_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1)))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (and (and (block_11_constructor_15_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_5_1 x_5_0))) true) true)) true) (block_12__14_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1))))


(declare-fun |block_13_return_constructor_15_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_14_constructor_15_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (and (and (block_12__14_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 2) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_5_1) true)))))) (and (not expr_11_1) (= error_1 3))) (block_14_constructor_15_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (block_14_constructor_15_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) (summary_3_constructor_15_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (and (and (block_12__14_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) (and (= error_1 error_0) (and (= expr_11_1 (= expr_9_0 expr_10_0)) (and (=> true true) (and (= expr_10_0 2) (and (=> true (and (>= expr_9_0 0) (<= expr_9_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_9_0 x_5_1) true))))))) true) (block_13_return_constructor_15_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (and (and (block_13_return_constructor_15_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) true) true) (summary_3_constructor_15_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1))))


(declare-fun |contract_initializer_15_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_16_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_5_1 x_5_0))) true) (contract_initializer_entry_16_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1))))


(declare-fun |summary_17_function_f__37_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int))
(=> (summary_4_function_f__37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_2 _20_2) (summary_17_function_f__37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 y_17_0 state_1 x_5_1 y_17_2 _20_2))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int))
(=> (and (and (contract_initializer_entry_16_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) (and (summary_17_function_f__37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_5_1 expr_3_0 state_1 x_5_1 y_17_2 _20_2) (and (=> true true) (and (= expr_3_0 2) (and true true))))) (> error_1 0)) (contract_initializer_15_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1))))


(declare-fun |contract_initializer_after_init_18_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_4_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int))
(=> (and (and (contract_initializer_entry_16_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) (and (= x_5_2 expr_4_0) (and (=> true (and (>= expr_4_0 0) (<= expr_4_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_4_0 _20_2) (and (= error_1 0) (and (summary_17_function_f__37_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_5_1 expr_3_0 state_1 x_5_1 y_17_2 _20_2) (and (=> true true) (and (= expr_3_0 2) (and true true))))))))) true) (contract_initializer_after_init_18_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_2))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_4_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int))
(=> (and (and (contract_initializer_after_init_18_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) (and (summary_3_constructor_15_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_5_1 state_2 x_5_2) true)) (> error_1 0)) (contract_initializer_15_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_2 x_5_2))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_4_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int))
(=> (and (and (contract_initializer_after_init_18_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) (and (= error_1 0) (and (summary_3_constructor_15_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_5_1 state_2 x_5_2) true))) true) (contract_initializer_15_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_2 x_5_2))))


(declare-fun |implicit_constructor_entry_19_C_38_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_4_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_5_2 x_5_0))) true) (and true (= x_5_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_19_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_2 x_5_2))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_4_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int))
(=> (and (and (implicit_constructor_entry_19_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) (and (contract_initializer_15_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_5_1 state_2 x_5_2) true)) (> error_1 0)) (summary_constructor_2_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_2 x_5_2))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_4_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int))
(=> (and (and (implicit_constructor_entry_19_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) (and (= error_1 0) (and (contract_initializer_15_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_5_1 state_2 x_5_2) true))) true) (summary_constructor_2_C_38_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_2 x_5_2))))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_4_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int))
(=> (and (and (summary_constructor_2_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_38_0 this_0 abi_0 crypto_0 state_1 x_5_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_4_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int) (y_17_3 Int))
(=> (and (and (summary_constructor_2_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_4_0)))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_4_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int) (y_17_3 Int))
(=> (and (and (summary_constructor_2_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 2))) error_target_5_0)))


(declare-fun |error_target_6_0| () Bool)
(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_4_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int) (y_17_3 Int))
(=> (and (and (summary_constructor_2_C_38_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_5_0 state_1 x_5_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 3))) error_target_6_0)))


(assert
(forall ( (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_1 Bool) (expr_23_0 Int) (expr_24_0 Int) (expr_25_1 Bool) (expr_29_0 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_34_0 Int) (expr_3_0 Int) (expr_4_0 Int) (expr_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (t_function_internal_view$_t_uint256_$returns$_t_uint256_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (x_5_0 Int) (x_5_1 Int) (x_5_2 Int) (y_17_0 Int) (y_17_1 Int) (y_17_2 Int) (y_17_3 Int))
(=> error_target_6_0 false)))
(check-sat)