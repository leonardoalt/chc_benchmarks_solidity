(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple(uint256,uint256)| 0)) (((|tuple(uint256,uint256)| (|tuple(uint256,uint256)_accessor_0| Int) (|tuple(uint256,uint256)_accessor_1| Int)))))
(declare-fun |interface_0_L_17_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_L_17_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_L_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_L_17_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_pub__8_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_4_function_pub__8_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_L_17_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_pub__8_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 _3_1))) (nondet_interface_1_L_17_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_5_function_inter__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_6_function_fu__33_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |interface_7_C_57_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_8_C_57_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_9_C_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_1 0) (nondet_interface_8_C_57_0 error_1 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_10_function_inter__16_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_11_function_fu__33_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |summary_12_function_f__56_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_13_function_f__56_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_8_C_57_0 error_1 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_1 0) (summary_13_function_f__56_57_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_8_C_57_0 error_2 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_14_function_pub__8_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_15_pub_7_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_11_1 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(block_14_function_pub__8_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1)))


(assert
(forall ( (_11_1 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_14_function_pub__8_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_15_pub_7_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1))))


(declare-fun |block_16_return_function_pub__8_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_11_1 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_15_pub_7_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (and (= _3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 7) (and (= _3_1 0) true))))) true) (block_16_return_function_pub__8_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2))))


(declare-fun |block_17_return_ghost_pub_6_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_11_1 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_17_return_ghost_pub_6_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2) (and (= _3_2 expr_5_0) (and (=> true true) (and (= expr_5_0 7) (and (= _3_1 0) true))))) true) (block_16_return_function_pub__8_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_2))))


(assert
(forall ( (_11_1 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_16_return_function_pub__8_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) true) true) (summary_3_function_pub__8_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1))))


(declare-fun |block_18_function_pub__8_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_11_1 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(block_18_function_pub__8_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1)))


(assert
(forall ( (_11_1 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_18_function_pub__8_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (and (summary_3_function_pub__8_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3 _3_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 2112861200)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 125)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 239)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 180)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 16)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_4_function_pub__8_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3 _3_1))))


(assert
(forall ( (_11_1 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (interface_0_L_17_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_pub__8_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _3_1) (= error_0 0))) (interface_0_L_17_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_19_function_inter__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_20_inter_15_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(block_19_function_inter__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_1)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_19_function_inter__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_20_inter_15_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_1))))


(declare-fun |block_21_return_function_inter__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_20_inter_15_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_1) (and (= _11_2 expr_13_0) (and (=> true true) (and (= expr_13_0 8) (and (= _11_1 0) true))))) true) (block_21_return_function_inter__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_2))))


(declare-fun |block_22_return_ghost_inter_14_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_22_return_ghost_inter_14_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_2) (and (= _11_2 expr_13_0) (and (=> true true) (and (= expr_13_0 8) (and (= _11_1 0) true))))) true) (block_21_return_function_inter__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_1 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_21_return_function_inter__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_1) true) true) (summary_5_function_inter__16_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_1))))


(declare-fun |block_23_function_fu__33_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_24_fu_32_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_22_0 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(block_23_function_fu__33_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_22_0 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_5_0 Int) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_23_function_fu__33_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_24_fu_32_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1))))


(declare-fun |block_25_return_function_fu__33_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |summary_26_function_inter__16_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_22_0 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (summary_5_function_inter__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 _11_2) (summary_26_function_inter__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 _11_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_22_0 Int) (_22_1 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_24_fu_32_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1) (and (summary_26_function_inter__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_2 _11_2) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 _3_1) (and (= state_2 (|state_type| fresh_balances_1_0)) (and (= _22_1 0) (and (= _20_1 0) true))))))) (> error_1 0)) (summary_6_function_fu__33_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 _20_1 _22_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_24_fu_32_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1) (and (= _22_2 (|tuple(uint256,uint256)_accessor_1| expr_30_1)) (and (= _20_2 (|tuple(uint256,uint256)_accessor_0| expr_30_1)) (and (= (|tuple(uint256,uint256)_accessor_1| expr_30_1) expr_29_0) (and (= (|tuple(uint256,uint256)_accessor_0| expr_30_1) expr_26_1) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 _11_2) (and (= error_1 0) (and (summary_26_function_inter__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_2 _11_2) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 _3_1) (and (= state_2 (|state_type| fresh_balances_1_0)) (and (= _22_1 0) (and (= _20_1 0) true)))))))))))))) true) (block_25_return_function_fu__33_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 _20_2 _22_2))))


(declare-fun |block_27_return_ghost_fu_31_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_27_return_ghost_fu_31_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 _20_2 _22_2) (and (= _22_2 (|tuple(uint256,uint256)_accessor_1| expr_30_1)) (and (= _20_2 (|tuple(uint256,uint256)_accessor_0| expr_30_1)) (and (= (|tuple(uint256,uint256)_accessor_1| expr_30_1) expr_29_0) (and (= (|tuple(uint256,uint256)_accessor_0| expr_30_1) expr_26_1) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 _11_2) (and (= error_1 0) (and (summary_26_function_inter__16_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_2 _11_2) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 _3_1) (and (= state_2 (|state_type| fresh_balances_1_0)) (and (= _22_1 0) (and (= _20_1 0) true)))))))))))))) true) (block_25_return_function_fu__33_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 _20_2 _22_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (block_25_return_function_fu__33_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1) true) true) (summary_6_function_fu__33_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1))))


(declare-fun |contract_initializer_28_L_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_29_L_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_29_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_30_L_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (contract_initializer_entry_29_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_30_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (contract_initializer_after_init_30_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_28_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_31_L_17_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_31_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (implicit_constructor_entry_31_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_28_L_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_L_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (implicit_constructor_entry_31_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_28_L_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_L_17_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (y_39_1 Int))
(=> (and (and (summary_constructor_2_L_17_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_L_17_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_32_function_inter__16_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_33_inter_15_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(block_32_function_inter__16_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_1)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_32_function_inter__16_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_33_inter_15_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_1))))


(declare-fun |block_34_return_function_inter__16_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_33_inter_15_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_1) (and (= _11_2 expr_13_0) (and (=> true true) (and (= expr_13_0 8) (and (= _11_1 0) true))))) true) (block_34_return_function_inter__16_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_2))))


(declare-fun |block_35_return_ghost_inter_14_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_35_return_ghost_inter_14_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_2) (and (= _11_2 expr_13_0) (and (=> true true) (and (= expr_13_0 8) (and (= _11_1 0) true))))) true) (block_34_return_function_inter__16_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_34_return_function_inter__16_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_1) true) true) (summary_10_function_inter__16_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _11_1))))


(declare-fun |block_36_function_fu__33_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_37_fu_32_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(block_36_function_fu__33_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_36_function_fu__33_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_37_fu_32_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1))))


(declare-fun |block_38_return_function_fu__33_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |summary_39_function_inter__16_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (summary_10_function_inter__16_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 _11_2) (summary_39_function_inter__16_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 _11_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_37_fu_32_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1) (and (summary_39_function_inter__16_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_2 _11_2) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 _3_3) (and (= state_2 (|state_type| fresh_balances_2_0)) (and (= _22_1 0) (and (= _20_1 0) true))))))) (> error_1 0)) (summary_11_function_fu__33_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 _20_1 _22_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_37_fu_32_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1) (and (= _22_2 (|tuple(uint256,uint256)_accessor_1| expr_30_1)) (and (= _20_2 (|tuple(uint256,uint256)_accessor_0| expr_30_1)) (and (= (|tuple(uint256,uint256)_accessor_1| expr_30_1) expr_29_0) (and (= (|tuple(uint256,uint256)_accessor_0| expr_30_1) expr_26_1) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 _11_2) (and (= error_1 0) (and (summary_39_function_inter__16_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_2 _11_2) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 _3_3) (and (= state_2 (|state_type| fresh_balances_2_0)) (and (= _22_1 0) (and (= _20_1 0) true)))))))))))))) true) (block_38_return_function_fu__33_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 _20_2 _22_2))))


(declare-fun |block_40_return_ghost_fu_31_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_40_return_ghost_fu_31_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 _20_2 _22_2) (and (= _22_2 (|tuple(uint256,uint256)_accessor_1| expr_30_1)) (and (= _20_2 (|tuple(uint256,uint256)_accessor_0| expr_30_1)) (and (= (|tuple(uint256,uint256)_accessor_1| expr_30_1) expr_29_0) (and (= (|tuple(uint256,uint256)_accessor_0| expr_30_1) expr_26_1) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 _11_2) (and (= error_1 0) (and (summary_39_function_inter__16_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_2 _11_2) (and (=> true (and (>= expr_26_1 0) (<= expr_26_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_26_1 _3_3) (and (= state_2 (|state_type| fresh_balances_2_0)) (and (= _22_1 0) (and (= _20_1 0) true)))))))))))))) true) (block_38_return_function_fu__33_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 _20_2 _22_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_38_return_function_fu__33_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1) true) true) (summary_11_function_fu__33_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_1 _22_1))))


(declare-fun |block_41_function_f__56_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |block_42_f_55_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(block_41_function_f__56_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_1 y_39_1)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_41_function_f__56_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_1 y_39_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_42_f_55_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_1 y_39_1))))


(declare-fun |block_43_return_function_f__56_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |summary_44_function_fu__33_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (summary_11_function_fu__33_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_2 _22_2) (summary_44_function_fu__33_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 _20_2 _22_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_42_f_55_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_1 y_39_1) (and (summary_44_function_fu__33_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _20_2 _22_2) (and (= y_39_1 0) (and (= x_37_1 0) true)))) (> error_1 0)) (summary_12_function_f__56_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_45_function_f__56_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_42_f_55_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_1 y_39_1) (and (= expr_46_1 (= expr_44_0 expr_45_0)) (and (=> true true) (and (= expr_45_0 7) (and (=> true (and (>= expr_44_0 0) (<= expr_44_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_44_0 x_37_2) (and (= y_39_2 (|tuple(uint256,uint256)_accessor_1| expr_41_1)) (and (= x_37_2 (|tuple(uint256,uint256)_accessor_0| expr_41_1)) (and (= (|tuple(uint256,uint256)_accessor_1| expr_41_1) _22_2) (and (= (|tuple(uint256,uint256)_accessor_0| expr_41_1) _20_2) (and (= error_1 0) (and (summary_44_function_fu__33_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _20_2 _22_2) (and (= y_39_1 0) (and (= x_37_1 0) true)))))))))))))) (and (not expr_46_1) (= error_2 3))) (block_45_function_f__56_57_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_2 y_39_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (block_45_function_f__56_57_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_2 y_39_2) (summary_12_function_f__56_57_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_46_function_f__56_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_42_f_55_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_1 y_39_1) (and (= expr_52_1 (= expr_50_0 expr_51_0)) (and (=> true true) (and (= expr_51_0 9) (and (=> true (and (>= expr_50_0 0) (<= expr_50_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_0 y_39_2) (and (= error_2 error_1) (and (= expr_46_1 (= expr_44_0 expr_45_0)) (and (=> true true) (and (= expr_45_0 7) (and (=> true (and (>= expr_44_0 0) (<= expr_44_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_44_0 x_37_2) (and (= y_39_2 (|tuple(uint256,uint256)_accessor_1| expr_41_1)) (and (= x_37_2 (|tuple(uint256,uint256)_accessor_0| expr_41_1)) (and (= (|tuple(uint256,uint256)_accessor_1| expr_41_1) _22_2) (and (= (|tuple(uint256,uint256)_accessor_0| expr_41_1) _20_2) (and (= error_1 0) (and (summary_44_function_fu__33_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _20_2 _22_2) (and (= y_39_1 0) (and (= x_37_1 0) true)))))))))))))))))))) (and (not expr_52_1) (= error_3 4))) (block_46_function_f__56_57_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_2 y_39_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (block_46_function_f__56_57_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_2 y_39_2) (summary_12_function_f__56_57_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_42_f_55_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_1 y_39_1) (and (= error_3 error_2) (and (= expr_52_1 (= expr_50_0 expr_51_0)) (and (=> true true) (and (= expr_51_0 9) (and (=> true (and (>= expr_50_0 0) (<= expr_50_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_50_0 y_39_2) (and (= error_2 error_1) (and (= expr_46_1 (= expr_44_0 expr_45_0)) (and (=> true true) (and (= expr_45_0 7) (and (=> true (and (>= expr_44_0 0) (<= expr_44_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_44_0 x_37_2) (and (= y_39_2 (|tuple(uint256,uint256)_accessor_1| expr_41_1)) (and (= x_37_2 (|tuple(uint256,uint256)_accessor_0| expr_41_1)) (and (= (|tuple(uint256,uint256)_accessor_1| expr_41_1) _22_2) (and (= (|tuple(uint256,uint256)_accessor_0| expr_41_1) _20_2) (and (= error_1 0) (and (summary_44_function_fu__33_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 _20_2 _22_2) (and (= y_39_1 0) (and (= x_37_1 0) true))))))))))))))))))))) true) (block_43_return_function_f__56_57_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_2 y_39_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_43_return_function_f__56_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_1 y_39_1) true) true) (summary_12_function_f__56_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_47_function_f__56_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(block_47_function_f__56_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_1 y_39_1)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (block_47_function_f__56_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_37_1 y_39_1) (and (summary_12_function_f__56_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_5_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_5_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_5_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_5_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_13_function_f__56_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (interface_7_C_57_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_13_function_f__56_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_7_C_57_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_48_C_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_49_C_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_49_C_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_50_C_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (contract_initializer_entry_49_C_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_50_C_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (contract_initializer_after_init_50_C_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_48_C_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_51_C_57_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_51_C_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (implicit_constructor_entry_51_C_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_48_C_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_9_C_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (implicit_constructor_entry_51_C_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_48_C_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_9_C_57_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (summary_constructor_9_C_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_7_C_57_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_6_0| () Bool)
(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> (and (and (interface_7_C_57_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_13_function_f__56_57_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 3))) error_target_6_0)))


(assert
(forall ( (_11_0 Int) (_11_1 Int) (_11_2 Int) (_11_3 Int) (_11_4 Int) (_20_0 Int) (_20_1 Int) (_20_2 Int) (_20_3 Int) (_22_0 Int) (_22_1 Int) (_22_2 Int) (_22_3 Int) (_3_0 Int) (_3_1 Int) (_3_2 Int) (_3_3 Int) (_3_4 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_13_0 Int) (expr_26_1 Int) (expr_29_0 Int) (expr_30_1 |tuple(uint256,uint256)|) (expr_41_1 |tuple(uint256,uint256)|) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (expr_50_0 Int) (expr_51_0 Int) (expr_52_1 Bool) (expr_5_0 Int) (fresh_balances_1_0 (Array Int Int)) (fresh_balances_2_0 (Array Int Int)) (funds_0_0 Int) (funds_5_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_37_0 Int) (x_37_1 Int) (x_37_2 Int) (x_37_3 Int) (y_39_0 Int) (y_39_1 Int) (y_39_2 Int) (y_39_3 Int))
(=> error_target_6_0 false)))
(check-sat)