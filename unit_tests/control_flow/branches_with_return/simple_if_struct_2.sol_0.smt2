(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|struct C.S| 0)) (((|struct C.S| (|struct C.S_accessor_x| Int)))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_C_52_0| (Int |abi_type| |crypto_type| |state_type| |struct C.S| ) Bool)
(declare-fun |nondet_interface_1_C_52_0| (Int Int |abi_type| |crypto_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(declare-fun |summary_constructor_2_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |struct C.S| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (s_6_0 |struct C.S|) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_52_0 error_0 this_0 abi_0 crypto_0 state_0 s_6_0 state_0 s_6_0))))


(declare-fun |summary_3_function_check__34_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(declare-fun |summary_4_function_check__34_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_52_0 error_0 this_0 abi_0 crypto_0 state_0 s_6_0 state_1 s_6_1) true) (and (= error_0 0) (summary_4_function_check__34_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 s_6_1 state_2 s_6_2))) (nondet_interface_1_C_52_0 error_1 this_0 abi_0 crypto_0 state_0 s_6_0 state_2 s_6_2))))


(declare-fun |summary_5_function_conditional_increment__51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(declare-fun |block_6_function_check__34_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(declare-fun |block_7_check_33_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_6_function_check__34_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_function_check__34_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= s_6_1 s_6_0))) true) true)) true) (block_7_check_33_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1))))


(declare-fun |block_8_return_function_check__34_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(declare-fun |summary_9_function_conditional_increment__51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_5_function_conditional_increment__51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_2 s_6_2) (summary_9_function_conditional_increment__51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_2 s_6_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_check_33_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (and (summary_9_function_conditional_increment__51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 s_6_1 state_2 s_6_2) (and (=> true expr_13_1) (and (= expr_13_1 (= expr_11_1 expr_12_0)) (and (=> true true) (and (= expr_12_0 0) (and (=> true (and (>= expr_11_1 0) (<= expr_11_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_1 (|struct C.S_accessor_x| expr_10_0)) (and (= expr_10_0 s_6_1) true))))))))) (> error_1 0)) (summary_3_function_check__34_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_2 s_6_2))))


(declare-fun |block_10_function_check__34_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_check_33_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (and (= expr_23_1 (= expr_21_1 expr_22_0)) (and (=> true true) (and (= expr_22_0 1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_1 (|struct C.S_accessor_x| expr_20_0)) (and (= expr_20_0 s_6_2) (and (= error_1 0) (and (summary_9_function_conditional_increment__51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 s_6_1 state_2 s_6_2) (and (=> true expr_13_1) (and (= expr_13_1 (= expr_11_1 expr_12_0)) (and (=> true true) (and (= expr_12_0 0) (and (=> true (and (>= expr_11_1 0) (<= expr_11_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_1 (|struct C.S_accessor_x| expr_10_0)) (and (= expr_10_0 s_6_1) true)))))))))))))))) (and (not expr_23_1) (= error_2 1))) (block_10_function_check__34_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_2 s_6_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_10_function_check__34_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_2 s_6_2) (summary_3_function_check__34_52_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_2 s_6_2))))


(declare-fun |block_11_function_check__34_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_check_33_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (and (= expr_30_1 (= expr_28_1 expr_29_0)) (and (=> true true) (and (= expr_29_0 0) (and (=> true (and (>= expr_28_1 0) (<= expr_28_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_1 (|struct C.S_accessor_x| expr_27_0)) (and (= expr_27_0 s_6_2) (and (= error_2 error_1) (and (= expr_23_1 (= expr_21_1 expr_22_0)) (and (=> true true) (and (= expr_22_0 1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_1 (|struct C.S_accessor_x| expr_20_0)) (and (= expr_20_0 s_6_2) (and (= error_1 0) (and (summary_9_function_conditional_increment__51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 s_6_1 state_2 s_6_2) (and (=> true expr_13_1) (and (= expr_13_1 (= expr_11_1 expr_12_0)) (and (=> true true) (and (= expr_12_0 0) (and (=> true (and (>= expr_11_1 0) (<= expr_11_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_1 (|struct C.S_accessor_x| expr_10_0)) (and (= expr_10_0 s_6_1) true))))))))))))))))))))))) (and (not expr_30_1) (= error_3 2))) (block_11_function_check__34_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_2 s_6_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_11_function_check__34_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_2 s_6_2) (summary_3_function_check__34_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_2 s_6_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_check_33_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (and (= error_3 error_2) (and (= expr_30_1 (= expr_28_1 expr_29_0)) (and (=> true true) (and (= expr_29_0 0) (and (=> true (and (>= expr_28_1 0) (<= expr_28_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_28_1 (|struct C.S_accessor_x| expr_27_0)) (and (= expr_27_0 s_6_2) (and (= error_2 error_1) (and (= expr_23_1 (= expr_21_1 expr_22_0)) (and (=> true true) (and (= expr_22_0 1) (and (=> true (and (>= expr_21_1 0) (<= expr_21_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_21_1 (|struct C.S_accessor_x| expr_20_0)) (and (= expr_20_0 s_6_2) (and (= error_1 0) (and (summary_9_function_conditional_increment__51_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 s_6_1 state_2 s_6_2) (and (=> true expr_13_1) (and (= expr_13_1 (= expr_11_1 expr_12_0)) (and (=> true true) (and (= expr_12_0 0) (and (=> true (and (>= expr_11_1 0) (<= expr_11_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_11_1 (|struct C.S_accessor_x| expr_10_0)) (and (= expr_10_0 s_6_1) true)))))))))))))))))))))))) true) (block_8_return_function_check__34_52_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_2 s_6_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_return_function_check__34_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) true) true) (summary_3_function_check__34_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1))))


(declare-fun |block_12_function_check__34_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_12_function_check__34_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_function_check__34_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (and (summary_3_function_check__34_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 s_6_1 state_3 s_6_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 2442674349)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 145)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 152)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 64)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 173)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= s_6_1 s_6_0))) true) true))))))) true) (summary_4_function_check__34_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_3 s_6_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_52_0 this_0 abi_0 crypto_0 state_0 s_6_0) true) (and (summary_4_function_check__34_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (= error_0 0))) (interface_0_C_52_0 this_0 abi_0 crypto_0 state_1 s_6_1))))


(declare-fun |block_13_function_conditional_increment__51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(declare-fun |block_14_conditional_increment_50_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_13_function_conditional_increment__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_function_conditional_increment__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= s_6_1 s_6_0))) true) true)) true) (block_14_conditional_increment_50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1))))


(declare-fun |block_15_return_function_conditional_increment__51_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(declare-fun |block_16_if_header_conditional_increment_43_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(declare-fun |block_17_if_true_conditional_increment_42_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(declare-fun |block_18_conditional_increment_50_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_conditional_increment_50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) true) true) (block_16_if_header_conditional_increment_43_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_if_header_conditional_increment_43_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (and (= expr_40_1 (= expr_38_1 expr_39_0)) (and (=> true true) (and (= expr_39_0 0) (and (=> true (and (>= expr_38_1 0) (<= expr_38_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_1 (|struct C.S_accessor_x| expr_37_0)) (and (= expr_37_0 s_6_1) true))))))) expr_40_1) (block_17_if_true_conditional_increment_42_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_if_header_conditional_increment_43_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (and (= expr_40_1 (= expr_38_1 expr_39_0)) (and (=> true true) (and (= expr_39_0 0) (and (=> true (and (>= expr_38_1 0) (<= expr_38_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_38_1 (|struct C.S_accessor_x| expr_37_0)) (and (= expr_37_0 s_6_1) true))))))) (not expr_40_1)) (block_18_conditional_increment_50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_17_if_true_conditional_increment_42_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) true) true) (block_15_return_function_conditional_increment__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1))))


(declare-fun |block_19_return_ghost_conditional_increment_41_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |struct C.S| |state_type| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_19_return_ghost_conditional_increment_41_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) true) true) (block_18_conditional_increment_50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 |struct C.S|) (expr_46_0 Int) (expr_47_1 |struct C.S|) (expr_48_1 |struct C.S|) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_18_conditional_increment_50_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (and (= s_6_2 expr_48_1) (and (= expr_48_1 expr_47_1) (and (= expr_44_0 s_6_1) (and (= expr_46_0 (|struct C.S_accessor_x| expr_47_1)) (and (=> true true) (and (= expr_46_0 1) true))))))) true) (block_15_return_function_conditional_increment__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 |struct C.S|) (expr_46_0 Int) (expr_47_1 |struct C.S|) (expr_48_1 |struct C.S|) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_15_return_function_conditional_increment__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) true) true) (summary_5_function_conditional_increment__51_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1))))


(declare-fun |contract_initializer_20_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |struct C.S| |struct C.S| ) Bool)
(declare-fun |contract_initializer_entry_21_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |struct C.S| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 |struct C.S|) (expr_46_0 Int) (expr_47_1 |struct C.S|) (expr_48_1 |struct C.S|) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= s_6_1 s_6_0))) (contract_initializer_entry_21_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_6_0 s_6_1))))


(declare-fun |contract_initializer_after_init_22_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |struct C.S| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 |struct C.S|) (expr_46_0 Int) (expr_47_1 |struct C.S|) (expr_48_1 |struct C.S|) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_21_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_6_0 s_6_1) true) true) (contract_initializer_after_init_22_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_6_0 s_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 |struct C.S|) (expr_46_0 Int) (expr_47_1 |struct C.S|) (expr_48_1 |struct C.S|) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_22_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_6_0 s_6_1) true) true) (contract_initializer_20_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_6_0 s_6_1))))


(declare-fun |implicit_constructor_entry_23_C_52_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |struct C.S| |struct C.S| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 |struct C.S|) (expr_46_0 Int) (expr_47_1 |struct C.S|) (expr_48_1 |struct C.S|) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= s_6_1 s_6_0))) (and true (= s_6_1 (|struct C.S| 0)))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_23_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_6_0 s_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 |struct C.S|) (expr_46_0 Int) (expr_47_1 |struct C.S|) (expr_48_1 |struct C.S|) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_23_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_6_0 s_6_1) (and (contract_initializer_20_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 s_6_1 s_6_2) true)) (> error_1 0)) (summary_constructor_2_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 s_6_0 s_6_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 |struct C.S|) (expr_46_0 Int) (expr_47_1 |struct C.S|) (expr_48_1 |struct C.S|) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_23_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_6_0 s_6_1) (and (= error_1 0) (and (contract_initializer_20_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 s_6_1 s_6_2) true))) true) (summary_constructor_2_C_52_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 s_6_0 s_6_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 |struct C.S|) (expr_46_0 Int) (expr_47_1 |struct C.S|) (expr_48_1 |struct C.S|) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 s_6_0 s_6_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_52_0 this_0 abi_0 crypto_0 state_1 s_6_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 |struct C.S|) (expr_46_0 Int) (expr_47_1 |struct C.S|) (expr_48_1 |struct C.S|) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_52_0 this_0 abi_0 crypto_0 state_0 s_6_0) true) (and (summary_4_function_check__34_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (= error_0 1))) error_target_4_0)))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 |struct C.S|) (expr_46_0 Int) (expr_47_1 |struct C.S|) (expr_48_1 |struct C.S|) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_52_0 this_0 abi_0 crypto_0 state_0 s_6_0) true) (and (summary_4_function_check__34_52_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 s_6_0 state_1 s_6_1) (= error_0 2))) error_target_5_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_10_0 |struct C.S|) (expr_11_1 Int) (expr_12_0 Int) (expr_13_1 Bool) (expr_17_1 |tuple()|) (expr_20_0 |struct C.S|) (expr_21_1 Int) (expr_22_0 Int) (expr_23_1 Bool) (expr_27_0 |struct C.S|) (expr_28_1 Int) (expr_29_0 Int) (expr_30_1 Bool) (expr_37_0 |struct C.S|) (expr_38_1 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 |struct C.S|) (expr_46_0 Int) (expr_47_1 |struct C.S|) (expr_48_1 |struct C.S|) (funds_3_0 Int) (s_6_0 |struct C.S|) (s_6_1 |struct C.S|) (s_6_2 |struct C.S|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_5_0 false)))
(check-sat)