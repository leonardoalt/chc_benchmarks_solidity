(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_37_0| (Int |abi_type| |crypto_type| |state_type| Int Bool ) Bool)
(declare-fun |nondet_interface_1_C_37_0| (Int Int |abi_type| |crypto_type| |state_type| Int Bool |state_type| Int Bool ) Bool)
(declare-fun |summary_constructor_2_C_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Bool |state_type| Int Bool Bool ) Bool)
(assert
(forall ( (a_2_0 Int) (abi_0 |abi_type|) (b_4_0 Bool) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_37_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 b_4_0 state_0 a_2_0 b_4_0))))


(declare-fun |summary_3_constructor_14_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Bool |state_type| Int Bool Bool ) Bool)
(declare-fun |summary_4_function_f__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool Int ) Bool)
(declare-fun |summary_5_function_f__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool Int ) Bool)
(assert
(forall ( (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_37_0 error_0 this_0 abi_0 crypto_0 state_0 a_2_0 b_4_0 state_1 a_2_1 b_4_1) true) (and (= error_0 0) (summary_5_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 b_4_1 state_2 a_2_2 b_4_2 c_17_1))) (nondet_interface_1_C_37_0 error_1 this_0 abi_0 crypto_0 state_0 a_2_0 b_4_0 state_2 a_2_2 b_4_2))))


(declare-fun |block_6_function_f__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool Int ) Bool)
(declare-fun |block_7_f_35_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_6_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_1 b_4_1 c_17_1)))


(assert
(forall ( (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_1 b_4_1 c_17_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= a_2_1 a_2_0)) (= b_4_1 b_4_0))) true) true)) true) (block_7_f_35_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_1 b_4_1 c_17_1))))


(declare-fun |block_8_return_function_f__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool Int ) Bool)
(declare-fun |block_9_function_f__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_f_35_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_1 b_4_1 c_17_1) (and (= expr_32_1 (>= expr_30_0 expr_31_0)) (and (=> true (and (>= expr_31_0 0) (<= expr_31_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_31_0 a_2_3) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 c_17_2) (and (= c_17_2 expr_27_1) (and (=> true (and (>= expr_27_1 0) (<= expr_27_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_1 expr_26_0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 c_17_1) (and (=> true (and (>= expr_26_0 0) (<= expr_26_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_0 (ite expr_20_0 expr_23_1 expr_25_1)) (and (= a_2_3 (ite expr_20_0 a_2_1 a_2_2)) (and (= a_2_2 (+ expr_24_0 1)) (and (=> (and true (not expr_20_0)) (and (>= expr_25_1 0) (<= expr_25_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_25_1 (+ expr_24_0 1)) (and (=> (and true (not expr_20_0)) (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 a_2_1) (and (=> (and true expr_20_0) (and (>= expr_23_1 0) (<= expr_23_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_1 (+ expr_21_0 expr_22_0)) (and (=> (and true expr_20_0) true) (and (= expr_22_0 10) (and (=> (and true expr_20_0) (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 a_2_1) (and (= expr_20_0 b_4_1) (and (= c_17_1 0) true))))))))))))))))))))))))))) (and (not expr_32_1) (= error_1 1))) (block_9_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_3 b_4_1 c_17_2))))


(assert
(forall ( (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_9_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_3 b_4_1 c_17_2) (summary_4_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_3 b_4_1 c_17_2))))


(assert
(forall ( (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_f_35_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_1 b_4_1 c_17_1) (and (= error_1 error_0) (and (= expr_32_1 (>= expr_30_0 expr_31_0)) (and (=> true (and (>= expr_31_0 0) (<= expr_31_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_31_0 a_2_3) (and (=> true (and (>= expr_30_0 0) (<= expr_30_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_30_0 c_17_2) (and (= c_17_2 expr_27_1) (and (=> true (and (>= expr_27_1 0) (<= expr_27_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_27_1 expr_26_0) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 c_17_1) (and (=> true (and (>= expr_26_0 0) (<= expr_26_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_0 (ite expr_20_0 expr_23_1 expr_25_1)) (and (= a_2_3 (ite expr_20_0 a_2_1 a_2_2)) (and (= a_2_2 (+ expr_24_0 1)) (and (=> (and true (not expr_20_0)) (and (>= expr_25_1 0) (<= expr_25_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_25_1 (+ expr_24_0 1)) (and (=> (and true (not expr_20_0)) (and (>= expr_24_0 0) (<= expr_24_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_24_0 a_2_1) (and (=> (and true expr_20_0) (and (>= expr_23_1 0) (<= expr_23_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_1 (+ expr_21_0 expr_22_0)) (and (=> (and true expr_20_0) true) (and (= expr_22_0 10) (and (=> (and true expr_20_0) (and (>= expr_21_0 0) (<= expr_21_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_0 a_2_1) (and (= expr_20_0 b_4_1) (and (= c_17_1 0) true)))))))))))))))))))))))))))) true) (block_8_return_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_3 b_4_1 c_17_2))))


(assert
(forall ( (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_return_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_1 b_4_1 c_17_1) true) true) (summary_4_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_1 b_4_1 c_17_1))))


(declare-fun |block_10_function_f__36_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool |state_type| Int Bool Int ) Bool)
(assert
(forall ( (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_10_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_1 b_4_1 c_17_1)))


(assert
(forall ( (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_10_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_1 b_4_1 c_17_1) (and (summary_4_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 a_2_1 b_4_1 state_3 a_2_2 b_4_2 c_17_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= a_2_1 a_2_0)) (= b_4_1 b_4_0))) true) true))))))) true) (summary_5_function_f__36_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_3 a_2_2 b_4_2 c_17_1))))


(assert
(forall ( (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_37_0 this_0 abi_0 crypto_0 state_0 a_2_0 b_4_0) true) (and (summary_5_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_1 b_4_1 c_17_1) (= error_0 0))) (interface_0_C_37_0 this_0 abi_0 crypto_0 state_1 a_2_1 b_4_1))))


(declare-fun |block_11_constructor_14_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Bool |state_type| Int Bool Bool ) Bool)
(declare-fun |block_12__13_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Bool |state_type| Int Bool Bool ) Bool)
(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_11_constructor_14_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_1)))


(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_constructor_14_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= a_2_1 a_2_0)) (= b_4_1 b_4_0))) (and true (= _b_6_1 _b_6_0))) true)) true) (block_12__13_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_1))))


(declare-fun |block_13_return_constructor_14_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Bool |state_type| Int Bool Bool ) Bool)
(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Bool) (expr_11_1 Bool) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12__13_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_1) (and (= b_4_2 expr_11_1) (and (= expr_11_1 expr_10_0) (and (= expr_9_0 b_4_1) (and (= expr_10_0 _b_6_1) (and true true)))))) true) (block_13_return_constructor_14_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_2 _b_6_1))))


(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Bool) (expr_11_1 Bool) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_return_constructor_14_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_1) true) true) (summary_3_constructor_14_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_1))))


(declare-fun |contract_initializer_14_C_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Bool |state_type| Int Bool Bool ) Bool)
(declare-fun |contract_initializer_entry_15_C_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Bool |state_type| Int Bool Bool ) Bool)
(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Bool) (expr_11_1 Bool) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= a_2_1 a_2_0)) (= b_4_1 b_4_0))) (and true (= _b_6_1 _b_6_0))) (contract_initializer_entry_15_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_1))))


(declare-fun |contract_initializer_after_init_16_C_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Bool |state_type| Int Bool Bool ) Bool)
(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Bool) (expr_11_1 Bool) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_15_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_1) true) true) (contract_initializer_after_init_16_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_1))))


(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (_b_6_2 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Bool) (expr_11_1 Bool) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_16_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_1) (and (summary_3_constructor_14_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 b_4_1 _b_6_1 state_2 a_2_2 b_4_2 _b_6_2) true)) (> error_1 0)) (contract_initializer_14_C_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_2 a_2_2 b_4_2 _b_6_2))))


(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (_b_6_2 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Bool) (expr_11_1 Bool) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_16_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_1) (and (= error_1 0) (and (summary_3_constructor_14_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 b_4_1 _b_6_1 state_2 a_2_2 b_4_2 _b_6_2) true))) true) (contract_initializer_14_C_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_2 a_2_2 b_4_2 _b_6_2))))


(declare-fun |implicit_constructor_entry_17_C_37_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Bool Bool |state_type| Int Bool Bool ) Bool)
(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (_b_6_2 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Bool) (expr_11_1 Bool) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and (and true (= a_2_2 a_2_0)) (= b_4_2 b_4_0))) (and true (= _b_6_2 _b_6_0))) (and (and true (= a_2_2 0)) (= b_4_2 false))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_17_C_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_2 a_2_2 b_4_2 _b_6_2))))


(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (_b_6_2 Bool) (_b_6_3 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Bool) (expr_11_1 Bool) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_17_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_2) (and (contract_initializer_14_C_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 b_4_1 _b_6_2 state_2 a_2_2 b_4_2 _b_6_3) true)) (> error_1 0)) (summary_constructor_2_C_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_2 a_2_2 b_4_2 _b_6_3))))


(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (_b_6_2 Bool) (_b_6_3 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Bool) (expr_11_1 Bool) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_17_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_2) (and (= error_1 0) (and (contract_initializer_14_C_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 a_2_1 b_4_1 _b_6_2 state_2 a_2_2 b_4_2 _b_6_3) true))) true) (summary_constructor_2_C_37_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_2 a_2_2 b_4_2 _b_6_3))))


(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (_b_6_2 Bool) (_b_6_3 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Bool) (expr_11_1 Bool) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 _b_6_0 state_1 a_2_1 b_4_1 _b_6_3) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_37_0 this_0 abi_0 crypto_0 state_1 a_2_1 b_4_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (_b_6_2 Bool) (_b_6_3 Bool) (_b_6_4 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Bool) (expr_11_1 Bool) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_37_0 this_0 abi_0 crypto_0 state_0 a_2_0 b_4_0) true) (and (summary_5_function_f__36_37_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 a_2_0 b_4_0 state_1 a_2_1 b_4_1 c_17_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (_b_6_0 Bool) (_b_6_1 Bool) (_b_6_2 Bool) (_b_6_3 Bool) (_b_6_4 Bool) (a_2_0 Int) (a_2_1 Int) (a_2_2 Int) (a_2_3 Int) (abi_0 |abi_type|) (b_4_0 Bool) (b_4_1 Bool) (b_4_2 Bool) (c_17_0 Int) (c_17_1 Int) (c_17_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Bool) (expr_11_1 Bool) (expr_19_0 Int) (expr_20_0 Bool) (expr_21_0 Int) (expr_22_0 Int) (expr_23_1 Int) (expr_24_0 Int) (expr_25_1 Int) (expr_26_0 Int) (expr_27_1 Int) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_3_0 false)))
(check-sat)