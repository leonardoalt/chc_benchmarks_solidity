(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|mapping(uint256 => uint256)_tuple| 0)) (((|mapping(uint256 => uint256)_tuple| (|mapping(uint256 => uint256)_tuple_accessor_array| (Array Int Int)) (|mapping(uint256 => uint256)_tuple_accessor_length| Int)))))
(declare-fun |interface_0_C_29_0| (Int |abi_type| |crypto_type| |state_type| |mapping(uint256 => uint256)_tuple| ) Bool)
(declare-fun |nondet_interface_1_C_29_0| (Int Int |abi_type| |crypto_type| |state_type| |mapping(uint256 => uint256)_tuple| |state_type| |mapping(uint256 => uint256)_tuple| ) Bool)
(declare-fun |summary_constructor_2_C_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |mapping(uint256 => uint256)_tuple| |mapping(uint256 => uint256)_tuple| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_29_0 error_0 this_0 abi_0 crypto_0 state_0 map_4_length_pair_0 state_0 map_4_length_pair_0))))


(declare-fun |summary_3_function_f__28_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |mapping(uint256 => uint256)_tuple| Int Int |state_type| |mapping(uint256 => uint256)_tuple| Int Int ) Bool)
(declare-fun |summary_4_function_f__28_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |mapping(uint256 => uint256)_tuple| Int Int |state_type| |mapping(uint256 => uint256)_tuple| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (y_8_0 Int) (y_8_1 Int))
(=> (and (and (nondet_interface_1_C_29_0 error_0 this_0 abi_0 crypto_0 state_0 map_4_length_pair_0 state_1 map_4_length_pair_1) true) (and (= error_0 0) (summary_4_function_f__28_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 map_4_length_pair_1 x_6_0 y_8_0 state_2 map_4_length_pair_2 x_6_1 y_8_1))) (nondet_interface_1_C_29_0 error_1 this_0 abi_0 crypto_0 state_0 map_4_length_pair_0 state_2 map_4_length_pair_2))))


(declare-fun |block_5_function_f__28_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |mapping(uint256 => uint256)_tuple| Int Int |state_type| |mapping(uint256 => uint256)_tuple| Int Int ) Bool)
(declare-fun |block_6_f_27_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |mapping(uint256 => uint256)_tuple| Int Int |state_type| |mapping(uint256 => uint256)_tuple| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (y_8_0 Int) (y_8_1 Int))
(block_5_function_f__28_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (y_8_0 Int) (y_8_1 Int))
(=> (and (and (block_5_function_f__28_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= map_4_length_pair_1 map_4_length_pair_0))) (and (and true (= x_6_1 x_6_0)) (= y_8_1 y_8_0))) true)) true) (block_6_f_27_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1))))


(declare-fun |block_7_return_function_f__28_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |mapping(uint256 => uint256)_tuple| Int Int |state_type| |mapping(uint256 => uint256)_tuple| Int Int ) Bool)
(declare-fun |block_8_function_f__28_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |mapping(uint256 => uint256)_tuple| Int Int |state_type| |mapping(uint256 => uint256)_tuple| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (y_8_0 Int) (y_8_1 Int))
(=> (and (and (block_6_f_27_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1) (and (= expr_14_1 (= expr_12_0 expr_13_0)) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 y_8_1) (and (=> true (and (>= expr_12_0 0) (<= expr_12_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_0 x_6_1) (and (and (>= y_8_1 0) (<= y_8_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (and (>= x_6_1 0) (<= x_6_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))) (and (not expr_14_1) (= error_1 1))) (block_8_function_f__28_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (y_8_0 Int) (y_8_1 Int))
(=> (block_8_function_f__28_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1) (summary_3_function_f__28_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1))))


(declare-fun |block_9_function_f__28_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |mapping(uint256 => uint256)_tuple| Int Int |state_type| |mapping(uint256 => uint256)_tuple| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (y_8_0 Int) (y_8_1 Int))
(=> (and (and (block_6_f_27_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1) (and (= expr_24_1 (= expr_20_1 expr_23_1)) (and (and (>= expr_23_1 0) (<= expr_23_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_23_1 0) (<= expr_23_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_1 (select (|mapping(uint256 => uint256)_tuple_accessor_array| map_4_length_pair_1) expr_22_0)) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 y_8_1) (and (= expr_21_length_pair_0 map_4_length_pair_1) (and (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_1 (select (|mapping(uint256 => uint256)_tuple_accessor_array| map_4_length_pair_1) expr_19_0)) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 x_6_1) (and (= expr_18_length_pair_0 map_4_length_pair_1) (and (= error_1 error_0) (and (= expr_14_1 (= expr_12_0 expr_13_0)) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 y_8_1) (and (=> true (and (>= expr_12_0 0) (<= expr_12_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_0 x_6_1) (and (and (>= y_8_1 0) (<= y_8_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (and (>= x_6_1 0) (<= x_6_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true)))))))))))))))))))))) (and (not expr_24_1) (= error_2 2))) (block_9_function_f__28_29_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (y_8_0 Int) (y_8_1 Int))
(=> (block_9_function_f__28_29_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1) (summary_3_function_f__28_29_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (y_8_0 Int) (y_8_1 Int))
(=> (and (and (block_6_f_27_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1) (and (= error_2 error_1) (and (= expr_24_1 (= expr_20_1 expr_23_1)) (and (and (>= expr_23_1 0) (<= expr_23_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_23_1 0) (<= expr_23_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_23_1 (select (|mapping(uint256 => uint256)_tuple_accessor_array| map_4_length_pair_1) expr_22_0)) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 y_8_1) (and (= expr_21_length_pair_0 map_4_length_pair_1) (and (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (=> true (and (>= expr_20_1 0) (<= expr_20_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_20_1 (select (|mapping(uint256 => uint256)_tuple_accessor_array| map_4_length_pair_1) expr_19_0)) (and (=> true (and (>= expr_19_0 0) (<= expr_19_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_19_0 x_6_1) (and (= expr_18_length_pair_0 map_4_length_pair_1) (and (= error_1 error_0) (and (= expr_14_1 (= expr_12_0 expr_13_0)) (and (=> true (and (>= expr_13_0 0) (<= expr_13_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_13_0 y_8_1) (and (=> true (and (>= expr_12_0 0) (<= expr_12_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_0 x_6_1) (and (and (>= y_8_1 0) (<= y_8_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (and (>= x_6_1 0) (<= x_6_1 115792089237316195423570985008687907853269984665640564039457584007913129639935)) true))))))))))))))))))))))) true) (block_7_return_function_f__28_29_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (y_8_0 Int) (y_8_1 Int))
(=> (and (and (block_7_return_function_f__28_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1) true) true) (summary_3_function_f__28_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1))))


(declare-fun |block_10_function_f__28_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |mapping(uint256 => uint256)_tuple| Int Int |state_type| |mapping(uint256 => uint256)_tuple| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (y_8_0 Int) (y_8_1 Int))
(block_10_function_f__28_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (funds_3_0 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (block_10_function_f__28_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1) (and (summary_3_function_f__28_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 map_4_length_pair_1 x_6_1 y_8_1 state_3 map_4_length_pair_2 x_6_2 y_8_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 332507694)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 19)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 209)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 170)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 46)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= map_4_length_pair_1 map_4_length_pair_0))) (and (and true (= x_6_1 x_6_0)) (= y_8_1 y_8_0))) true))))))) true) (summary_4_function_f__28_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_3 map_4_length_pair_2 x_6_2 y_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (funds_3_0 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (interface_0_C_29_0 this_0 abi_0 crypto_0 state_0 map_4_length_pair_0) true) (and (summary_4_function_f__28_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1) (= error_0 0))) (interface_0_C_29_0 this_0 abi_0 crypto_0 state_1 map_4_length_pair_1))))


(declare-fun |contract_initializer_11_C_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |mapping(uint256 => uint256)_tuple| |mapping(uint256 => uint256)_tuple| ) Bool)
(declare-fun |contract_initializer_entry_12_C_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |mapping(uint256 => uint256)_tuple| |mapping(uint256 => uint256)_tuple| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (funds_3_0 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= map_4_length_pair_1 map_4_length_pair_0))) (contract_initializer_entry_12_C_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 map_4_length_pair_0 map_4_length_pair_1))))


(declare-fun |contract_initializer_after_init_13_C_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |mapping(uint256 => uint256)_tuple| |mapping(uint256 => uint256)_tuple| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (funds_3_0 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (contract_initializer_entry_12_C_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 map_4_length_pair_0 map_4_length_pair_1) true) true) (contract_initializer_after_init_13_C_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 map_4_length_pair_0 map_4_length_pair_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (funds_3_0 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (contract_initializer_after_init_13_C_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 map_4_length_pair_0 map_4_length_pair_1) true) true) (contract_initializer_11_C_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 map_4_length_pair_0 map_4_length_pair_1))))


(declare-fun |implicit_constructor_entry_14_C_29_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| |mapping(uint256 => uint256)_tuple| |mapping(uint256 => uint256)_tuple| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (funds_3_0 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= map_4_length_pair_1 map_4_length_pair_0))) (and true (= map_4_length_pair_1 (|mapping(uint256 => uint256)_tuple| ((as const (Array Int Int)) 0) 0)))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_14_C_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 map_4_length_pair_0 map_4_length_pair_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (funds_3_0 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (implicit_constructor_entry_14_C_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 map_4_length_pair_0 map_4_length_pair_1) (and (contract_initializer_11_C_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 map_4_length_pair_1 map_4_length_pair_2) true)) (> error_1 0)) (summary_constructor_2_C_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 map_4_length_pair_0 map_4_length_pair_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (funds_3_0 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (implicit_constructor_entry_14_C_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 map_4_length_pair_0 map_4_length_pair_1) (and (= error_1 0) (and (contract_initializer_11_C_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 map_4_length_pair_1 map_4_length_pair_2) true))) true) (summary_constructor_2_C_29_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 map_4_length_pair_0 map_4_length_pair_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (funds_3_0 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (summary_constructor_2_C_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 map_4_length_pair_0 map_4_length_pair_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_29_0 this_0 abi_0 crypto_0 state_1 map_4_length_pair_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (funds_3_0 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> (and (and (interface_0_C_29_0 this_0 abi_0 crypto_0 state_0 map_4_length_pair_0) true) (and (summary_4_function_f__28_29_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 map_4_length_pair_0 x_6_0 y_8_0 state_1 map_4_length_pair_1 x_6_1 y_8_1) (= error_0 1))) error_target_4_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_12_0 Int) (expr_13_0 Int) (expr_14_1 Bool) (expr_18_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_19_0 Int) (expr_20_1 Int) (expr_21_length_pair_0 |mapping(uint256 => uint256)_tuple|) (expr_22_0 Int) (expr_23_1 Int) (expr_24_1 Bool) (funds_3_0 Int) (map_4_length_pair_0 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_1 |mapping(uint256 => uint256)_tuple|) (map_4_length_pair_2 |mapping(uint256 => uint256)_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (y_8_0 Int) (y_8_1 Int) (y_8_2 Int))
(=> error_target_4_0 false)))
(check-sat)