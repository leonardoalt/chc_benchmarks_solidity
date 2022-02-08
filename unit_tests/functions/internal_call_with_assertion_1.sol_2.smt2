(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_C_60_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_60_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_1_C_60_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_3_constructor_18_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_4_function_f__40_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_5_function_f__40_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_1_C_60_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_0 0) (summary_5_function_f__40_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_1_C_60_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |summary_6_function_g__59_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_7_function_f__40_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_8_f_39_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_1 Int))
(block_7_function_f__40_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_1 Int))
(=> (and (and (block_7_function_f__40_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_8_f_39_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_9_return_function_f__40_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_10_function_f__40_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_1 Int))
(=> (and (and (block_8_f_39_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_24_1 (= expr_22_0 expr_23_0)) (and (=> true true) (and (= expr_23_0 1) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 x_2_1) true)))))) (and (not expr_24_1) (= error_1 1))) (block_10_function_f__40_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_4_1 Int))
(=> (block_10_function_f__40_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_4_function_f__40_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |summary_11_function_g__59_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (summary_6_function_g__59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3) (summary_11_function_g__59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (and (and (block_8_f_39_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_11_function_g__59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_2_2 state_2 x_2_3) (and (= x_2_2 (+ expr_27_0 1)) (and (=> true (and (>= expr_28_1 0) (<= expr_28_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_1 (+ expr_27_0 1)) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_2_1) (and (= error_1 error_0) (and (= expr_24_1 (= expr_22_0 expr_23_0)) (and (=> true true) (and (= expr_23_0 1) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 x_2_1) true))))))))))))) (> error_2 0)) (summary_4_function_f__40_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(declare-fun |block_12_function_f__40_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (and (and (block_8_f_39_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_36_1 (= expr_34_0 expr_35_0)) (and (=> true true) (and (= expr_35_0 1) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 x_2_3) (and (= error_2 0) (and (summary_11_function_g__59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_2_2 state_2 x_2_3) (and (= x_2_2 (+ expr_27_0 1)) (and (=> true (and (>= expr_28_1 0) (<= expr_28_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_1 (+ expr_27_0 1)) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_2_1) (and (= error_1 error_0) (and (= expr_24_1 (= expr_22_0 expr_23_0)) (and (=> true true) (and (= expr_23_0 1) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 x_2_1) true))))))))))))))))))) (and (not expr_36_1) (= error_3 2))) (block_12_function_f__40_60_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (block_12_function_f__40_60_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3) (summary_4_function_f__40_60_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (and (and (block_8_f_39_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_3 error_2) (and (= expr_36_1 (= expr_34_0 expr_35_0)) (and (=> true true) (and (= expr_35_0 1) (and (=> true (and (>= expr_34_0 0) (<= expr_34_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_34_0 x_2_3) (and (= error_2 0) (and (summary_11_function_g__59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_2_2 state_2 x_2_3) (and (= x_2_2 (+ expr_27_0 1)) (and (=> true (and (>= expr_28_1 0) (<= expr_28_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_1 (+ expr_27_0 1)) (and (=> true (and (>= expr_27_0 0) (<= expr_27_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_0 x_2_1) (and (= error_1 error_0) (and (= expr_24_1 (= expr_22_0 expr_23_0)) (and (=> true true) (and (= expr_23_0 1) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 x_2_1) true)))))))))))))))))))) true) (block_9_return_function_f__40_60_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (and (and (block_9_return_function_f__40_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_4_function_f__40_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_13_function_f__40_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(block_13_function_f__40_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (and (and (block_13_function_f__40_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_4_function_f__40_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_5_function_f__40_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (and (and (interface_0_C_60_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_5_function_f__40_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_0_C_60_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_14_function_g__59_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_15_g_58_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(block_14_function_g__59_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (and (and (block_14_function_g__59_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_15_g_58_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_16_return_function_g__59_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_17_function_g__59_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (and (and (block_15_g_58_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_46_1 (= expr_44_0 expr_45_0)) (and (=> true true) (and (= expr_45_0 2) (and (=> true (and (>= expr_44_0 0) (<= expr_44_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_44_0 x_2_1) true)))))) (and (not expr_46_1) (= error_1 4))) (block_17_function_g__59_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (block_17_function_g__59_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_6_function_g__59_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_18_function_g__59_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (and (and (block_15_g_58_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_55_1 (= expr_53_0 expr_54_0)) (and (=> true true) (and (= expr_54_0 1) (and (=> true (and (>= expr_53_0 0) (<= expr_53_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_53_0 x_2_2) (and (= x_2_2 (- expr_49_0 1)) (and (=> true (and (>= expr_50_1 0) (<= expr_50_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_1 (- expr_49_0 1)) (and (=> true (and (>= expr_49_0 0) (<= expr_49_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_49_0 x_2_1) (and (= error_1 error_0) (and (= expr_46_1 (= expr_44_0 expr_45_0)) (and (=> true true) (and (= expr_45_0 2) (and (=> true (and (>= expr_44_0 0) (<= expr_44_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_44_0 x_2_1) true))))))))))))))))) (and (not expr_55_1) (= error_2 5))) (block_18_function_g__59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (block_18_function_g__59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2) (summary_6_function_g__59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (and (and (block_15_g_58_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_2 error_1) (and (= expr_55_1 (= expr_53_0 expr_54_0)) (and (=> true true) (and (= expr_54_0 1) (and (=> true (and (>= expr_53_0 0) (<= expr_53_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_53_0 x_2_2) (and (= x_2_2 (- expr_49_0 1)) (and (=> true (and (>= expr_50_1 0) (<= expr_50_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_1 (- expr_49_0 1)) (and (=> true (and (>= expr_49_0 0) (<= expr_49_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_49_0 x_2_1) (and (= error_1 error_0) (and (= expr_46_1 (= expr_44_0 expr_45_0)) (and (=> true true) (and (= expr_45_0 2) (and (=> true (and (>= expr_44_0 0) (<= expr_44_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_44_0 x_2_1) true)))))))))))))))))) true) (block_16_return_function_g__59_60_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_1 Int))
(=> (and (and (block_16_return_function_g__59_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_6_function_g__59_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_19_constructor_18_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_20__17_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int))
(block_19_constructor_18_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int))
(=> (and (and (block_19_constructor_18_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= y_4_1 y_4_0))) true)) true) (block_20__17_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(declare-fun |block_21_return_constructor_18_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_22_constructor_18_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int))
(=> (and (and (block_20__17_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_2_1) (and (and (>= y_4_1 0) (<= y_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))) (and (not expr_10_1) (= error_1 6))) (block_22_constructor_18_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int))
(=> (block_22_constructor_18_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (summary_3_constructor_18_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int))
(=> (and (and (block_20__17_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (= x_2_2 expr_15_1) (and (=> true (and (>= expr_15_1 0) (<= expr_15_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_15_1 expr_14_0) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 x_2_1) (and (=> true true) (and (= expr_14_0 1) (and (= error_1 error_0) (and (= expr_10_1 (= expr_8_0 expr_9_0)) (and (=> true true) (and (= expr_9_0 0) (and (=> true (and (>= expr_8_0 0) (<= expr_8_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_8_0 x_2_1) (and (and (>= y_4_1 0) (<= y_4_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))))))))) true) (block_21_return_constructor_18_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_2 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int))
(=> (and (and (block_21_return_constructor_18_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) true) true) (summary_3_constructor_18_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(declare-fun |contract_initializer_23_C_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_24_C_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= y_4_1 y_4_0))) (contract_initializer_entry_24_C_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(declare-fun |contract_initializer_after_init_25_C_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int))
(=> (and (and (contract_initializer_entry_24_C_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) true) true) (contract_initializer_after_init_25_C_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int))
(=> (and (and (contract_initializer_after_init_25_C_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (summary_3_constructor_18_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_1 state_2 x_2_2 y_4_2) true)) (> error_1 0)) (contract_initializer_23_C_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int))
(=> (and (and (contract_initializer_after_init_25_C_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_1) (and (= error_1 0) (and (summary_3_constructor_18_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_1 state_2 x_2_2 y_4_2) true))) true) (contract_initializer_23_C_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_2))))


(declare-fun |implicit_constructor_entry_26_C_60_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= x_2_2 x_2_0))) (and true (= y_4_2 y_4_0))) (and true (= x_2_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_26_C_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int))
(=> (and (and (implicit_constructor_entry_26_C_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_2) (and (contract_initializer_23_C_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_2 state_2 x_2_2 y_4_3) true)) (> error_1 0)) (summary_constructor_2_C_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int))
(=> (and (and (implicit_constructor_entry_26_C_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_2) (and (= error_1 0) (and (contract_initializer_23_C_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 y_4_2 state_2 x_2_2 y_4_3) true))) true) (summary_constructor_2_C_60_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_2 x_2_2 y_4_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int))
(=> (and (and (summary_constructor_2_C_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 y_4_0 state_1 x_2_1 y_4_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_60_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |error_target_7_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int))
(=> (and (and (interface_0_C_60_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_5_function_f__40_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 1))) error_target_7_0)))


(declare-fun |error_target_8_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int))
(=> (and (and (interface_0_C_60_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_5_function_f__40_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 2))) error_target_8_0)))


(declare-fun |error_target_9_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int))
(=> (and (and (interface_0_C_60_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_5_function_f__40_60_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 4))) error_target_9_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_1 Bool) (expr_13_0 Int) (expr_14_0 Int) (expr_15_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_27_0 Int) (expr_28_1 Int) (expr_31_1 |tuple()|) (expr_34_0 Int) (expr_35_0 Int) (expr_36_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_49_0 Int) (expr_50_1 Int) (expr_53_0 Int) (expr_54_0 Int) (expr_55_1 Bool) (expr_8_0 Int) (expr_9_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_4_0 Int) (y_4_1 Int) (y_4_2 Int) (y_4_3 Int) (y_4_4 Int))
(=> error_target_9_0 false)))
(check-sat)