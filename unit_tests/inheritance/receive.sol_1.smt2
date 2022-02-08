(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_A_23_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_A_23_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_1_A_23_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_3_receive_12_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_4_receive_12_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_1_A_23_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_0 0) (summary_4_receive_12_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_1_A_23_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |summary_5_function_g__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_6_function_g__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_1_A_23_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_1 0) (summary_6_function_g__22_23_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 state_2 x_2_2))) (nondet_interface_1_A_23_0 error_2 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |interface_7_B_39_0| (Int |abi_type| |crypto_type| |state_type| Int Int ) Bool)
(declare-fun |nondet_interface_8_B_39_0| (Int Int |abi_type| |crypto_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_constructor_9_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int))
(=> (= error_2 0) (nondet_interface_8_B_39_0 error_2 this_0 abi_0 crypto_0 state_0 y_27_0 x_2_0 state_0 y_27_0 x_2_0))))


(declare-fun |summary_10_receive_12_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_11_function_g__22_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_12_function_g__22_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (nondet_interface_8_B_39_0 error_2 this_0 abi_0 crypto_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) true) (and (= error_2 0) (summary_12_function_g__22_39_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 y_27_1 x_2_1 state_2 y_27_2 x_2_2))) (nondet_interface_8_B_39_0 error_3 this_0 abi_0 crypto_0 state_0 y_27_0 x_2_0 state_2 y_27_2 x_2_2))))


(declare-fun |summary_13_receive_38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_14_receive_38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (nondet_interface_8_B_39_0 error_3 this_0 abi_0 crypto_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) true) (and (= error_3 0) (summary_14_receive_38_39_0 error_4 this_0 abi_0 crypto_0 tx_0 state_1 y_27_1 x_2_1 state_2 y_27_2 x_2_2))) (nondet_interface_8_B_39_0 error_4 this_0 abi_0 crypto_0 state_0 y_27_0 x_2_0 state_2 y_27_2 x_2_2))))


(declare-fun |block_15_receive_12_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_16__11_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(block_15_receive_12_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (block_15_receive_12_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_16__11_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_17_return_receive_12_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_18_receive_12_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (block_16__11_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_8_1 (= expr_6_0 expr_7_0)) (and (=> true true) (and (= expr_7_0 1) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 x_2_1) true)))))) (and (not expr_8_1) (= error_1 1))) (block_18_receive_12_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (block_18_receive_12_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_3_receive_12_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (block_16__11_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 error_0) (and (= expr_8_1 (= expr_6_0 expr_7_0)) (and (=> true true) (and (= expr_7_0 1) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 x_2_1) true))))))) true) (block_17_return_receive_12_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (block_17_return_receive_12_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_3_receive_12_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_19_receive_12_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(block_19_receive_12_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (block_19_receive_12_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_3_receive_12_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) true) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_4_receive_12_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (interface_0_A_23_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_4_receive_12_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_0_A_23_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_20_function_g__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_21_g_21_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(block_20_function_g__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (block_20_function_g__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true)) true) (block_21_g_21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_22_return_function_g__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_23_function_g__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (block_21_g_21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= expr_18_1 (= expr_16_0 expr_17_0)) (and (=> true true) (and (= expr_17_0 1) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_0 x_2_1) true)))))) (and (not expr_18_1) (= error_1 3))) (block_23_function_g__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (block_23_function_g__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (summary_5_function_g__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (block_21_g_21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (= error_1 error_0) (and (= expr_18_1 (= expr_16_0 expr_17_0)) (and (=> true true) (and (= expr_17_0 1) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_0 x_2_1) true))))))) true) (block_22_return_function_g__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (block_22_return_function_g__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) true) true) (summary_5_function_g__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1))))


(declare-fun |block_24_function_g__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(block_24_function_g__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (block_24_function_g__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (and (summary_5_function_g__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 state_3 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_4_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_4_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_4_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_4_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) true) true))))))) true) (summary_6_function_g__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_3 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (interface_0_A_23_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_6_function_g__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 0))) (interface_0_A_23_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |contract_initializer_25_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_26_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_26_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_27_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (contract_initializer_entry_26_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_27_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (contract_initializer_after_init_27_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_25_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_28_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_28_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (implicit_constructor_entry_28_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_25_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_2_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (implicit_constructor_entry_28_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_1 0) (and (contract_initializer_25_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))) true) (summary_constructor_2_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int))
(=> (and (and (summary_constructor_2_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_A_23_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |block_29_receive_12_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_30__11_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(block_29_receive_12_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_29_receive_12_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_27_1 y_27_0)) (= x_2_1 x_2_0))) true) true)) true) (block_30__11_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(declare-fun |block_31_return_receive_12_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_32_receive_12_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_30__11_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (and (= expr_8_1 (= expr_6_0 expr_7_0)) (and (=> true true) (and (= expr_7_0 1) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 x_2_1) true)))))) (and (not expr_8_1) (= error_1 5))) (block_32_receive_12_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (block_32_receive_12_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (summary_10_receive_12_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_30__11_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (and (= error_1 error_0) (and (= expr_8_1 (= expr_6_0 expr_7_0)) (and (=> true true) (and (= expr_7_0 1) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 x_2_1) true))))))) true) (block_31_return_receive_12_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_31_return_receive_12_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) true) true) (summary_10_receive_12_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(declare-fun |block_33_function_g__22_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_34_g_21_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(block_33_function_g__22_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_33_function_g__22_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_27_1 y_27_0)) (= x_2_1 x_2_0))) true) true)) true) (block_34_g_21_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(declare-fun |block_35_return_function_g__22_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_36_function_g__22_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_34_g_21_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (and (= expr_18_1 (= expr_16_0 expr_17_0)) (and (=> true true) (and (= expr_17_0 1) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_0 x_2_1) true)))))) (and (not expr_18_1) (= error_1 6))) (block_36_function_g__22_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (block_36_function_g__22_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (summary_11_function_g__22_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_34_g_21_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (and (= error_1 error_0) (and (= expr_18_1 (= expr_16_0 expr_17_0)) (and (=> true true) (and (= expr_17_0 1) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_0 x_2_1) true))))))) true) (block_35_return_function_g__22_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_35_return_function_g__22_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) true) true) (summary_11_function_g__22_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(declare-fun |block_37_function_g__22_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(block_37_function_g__22_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_37_function_g__22_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (and (summary_11_function_g__22_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 y_27_1 x_2_1 state_3 y_27_2 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_7_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_7_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_7_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_7_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_27_1 y_27_0)) (= x_2_1 x_2_0))) true) true))))))) true) (summary_12_function_g__22_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_3 y_27_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (interface_7_B_39_0 this_0 abi_0 crypto_0 state_0 y_27_0 x_2_0) true) (and (summary_12_function_g__22_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (= error_0 0))) (interface_7_B_39_0 this_0 abi_0 crypto_0 state_1 y_27_1 x_2_1))))


(declare-fun |block_38_receive_38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_39__37_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(block_38_receive_38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_38_receive_38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_27_1 y_27_0)) (= x_2_1 x_2_0))) true) true)) true) (block_39__37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(declare-fun |block_40_return_receive_38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_41_receive_38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_39__37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (and (= expr_34_1 (= expr_32_0 expr_33_0)) (and (=> true true) (and (= expr_33_0 1) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 x_2_1) true)))))) (and (not expr_34_1) (= error_1 8))) (block_41_receive_38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (block_41_receive_38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (summary_13_receive_38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_39__37_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (and (= error_1 error_0) (and (= expr_34_1 (= expr_32_0 expr_33_0)) (and (=> true true) (and (= expr_33_0 1) (and (=> true (and (>= expr_32_0 0) (<= expr_32_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_32_0 x_2_1) true))))))) true) (block_40_return_receive_38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_40_return_receive_38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) true) true) (summary_13_receive_38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1))))


(declare-fun |block_42_receive_38_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(block_42_receive_38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (block_42_receive_38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (and (summary_13_receive_38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 y_27_1 x_2_1 state_3 y_27_2 x_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_9_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_9_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_9_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_9_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) true) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_27_1 y_27_0)) (= x_2_1 x_2_0))) true) true))))))) true) (summary_14_receive_38_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_3 y_27_2 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (interface_7_B_39_0 this_0 abi_0 crypto_0 state_0 y_27_0 x_2_0) true) (and (summary_14_receive_38_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 y_27_0 x_2_0 state_1 y_27_1 x_2_1) (= error_0 0))) (interface_7_B_39_0 this_0 abi_0 crypto_0 state_1 y_27_1 x_2_1))))


(declare-fun |contract_initializer_43_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_44_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_27_1 y_27_0)) (= x_2_1 x_2_0))) (contract_initializer_entry_44_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_27_0 x_2_0 y_27_1 x_2_1))))


(declare-fun |contract_initializer_after_init_45_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (contract_initializer_entry_44_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_27_0 x_2_0 y_27_1 x_2_1) true) true) (contract_initializer_after_init_45_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_27_0 x_2_0 y_27_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (contract_initializer_after_init_45_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_27_0 x_2_0 y_27_1 x_2_1) true) true) (contract_initializer_43_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_27_0 x_2_0 y_27_1 x_2_1))))


(declare-fun |contract_initializer_46_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_47_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_47_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_48_A_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (contract_initializer_entry_47_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_48_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (contract_initializer_after_init_48_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_46_A_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_49_B_39_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= y_27_1 y_27_0)) (= x_2_1 x_2_0))) (and (and true (= y_27_1 0)) (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_49_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_27_0 x_2_0 y_27_1 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (implicit_constructor_entry_49_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_27_0 x_2_0 y_27_1 x_2_1) (and (contract_initializer_46_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_9_B_39_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 y_27_0 x_2_0 y_27_1 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (implicit_constructor_entry_49_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_27_0 x_2_0 y_27_1 x_2_1) (and (contract_initializer_43_B_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 y_27_1 x_2_2 y_27_2 x_2_3) (and (= error_1 0) (and (contract_initializer_46_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)))) (> error_2 0)) (summary_constructor_9_B_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 y_27_0 x_2_0 y_27_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (implicit_constructor_entry_49_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_27_0 x_2_0 y_27_1 x_2_1) (and (= error_2 0) (and (contract_initializer_43_B_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_2 state_3 y_27_1 x_2_2 y_27_2 x_2_3) (and (= error_1 0) (and (contract_initializer_46_A_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))))) true) (summary_constructor_9_B_39_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_3 y_27_0 x_2_0 y_27_2 x_2_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (summary_constructor_9_B_39_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 y_27_0 x_2_0 y_27_1 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_7_B_39_0 this_0 abi_0 crypto_0 state_1 y_27_1 x_2_1))))


(declare-fun |error_target_10_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> (and (and (interface_0_A_23_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_4_receive_12_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 state_1 x_2_1) (= error_0 1))) error_target_10_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_32_0 Int) (expr_33_0 Int) (expr_34_1 Bool) (expr_6_0 Int) (expr_7_0 Int) (expr_8_1 Bool) (funds_2_0 Int) (funds_4_0 Int) (funds_7_0 Int) (funds_9_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int) (x_2_3 Int) (y_27_0 Int) (y_27_1 Int) (y_27_2 Int) (y_27_3 Int))
(=> error_target_10_0 false)))
(check-sat)