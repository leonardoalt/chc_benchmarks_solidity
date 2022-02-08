(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_D_4_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_D_4_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_D_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_D_4_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_d__3_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_4_function_d__3_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_D_4_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_d__3_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_D_4_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |interface_5_C_54_0| (Int |abi_type| |crypto_type| |state_type| Int Int ) Bool)
(declare-fun |nondet_interface_6_C_54_0| (Int Int |abi_type| |crypto_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_constructor_7_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int))
(=> (= error_1 0) (nondet_interface_6_C_54_0 error_1 this_0 abi_0 crypto_0 state_0 x_6_0 d_9_0 state_0 x_6_0 d_9_0))))


(declare-fun |summary_8_function_set__19_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |summary_9_function_set__19_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (error_0 Int) (error_1 Int) (error_2 Int) (n_11_0 Int) (n_11_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (nondet_interface_6_C_54_0 error_1 this_0 abi_0 crypto_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) true) (and (= error_1 0) (summary_9_function_set__19_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 x_6_1 d_9_1 n_11_0 state_2 x_6_2 d_9_2 n_11_1))) (nondet_interface_6_C_54_0 error_2 this_0 abi_0 crypto_0 state_0 x_6_0 d_9_0 state_2 x_6_2 d_9_2))))


(declare-fun |summary_10_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_11_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (n_11_0 Int) (n_11_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (nondet_interface_6_C_54_0 error_2 this_0 abi_0 crypto_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) true) (and (= error_2 0) (summary_11_function_f__53_54_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 x_6_1 d_9_1 state_2 x_6_2 d_9_2))) (nondet_interface_6_C_54_0 error_3 this_0 abi_0 crypto_0 state_0 x_6_0 d_9_0 state_2 x_6_2 d_9_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (n_11_0 Int) (n_11_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and true (= error_0 0)) (summary_3_function_d__3_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_12_D_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_13_D_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (n_11_0 Int) (n_11_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_13_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_14_D_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (n_11_0 Int) (n_11_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (contract_initializer_entry_13_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_14_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (n_11_0 Int) (n_11_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (contract_initializer_after_init_14_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_12_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_15_D_4_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (n_11_0 Int) (n_11_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_15_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (n_11_0 Int) (n_11_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (implicit_constructor_entry_15_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_12_D_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_D_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (n_11_0 Int) (n_11_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int))
(=> (and (and (implicit_constructor_entry_15_D_4_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_12_D_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_D_4_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(declare-fun |block_16_function_set__19_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_17_set_18_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(block_16_function_set__19_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 n_11_0 state_1 x_6_1 d_9_1 n_11_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_16_function_set__19_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 n_11_0 state_1 x_6_1 d_9_1 n_11_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_6_1 x_6_0)) (= d_9_1 d_9_0))) (and true (= n_11_1 n_11_0))) true)) true) (block_17_set_18_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 n_11_0 state_1 x_6_1 d_9_1 n_11_1))))


(declare-fun |block_18_return_function_set__19_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_17_set_18_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 n_11_0 state_1 x_6_1 d_9_1 n_11_1) (and (= x_6_2 expr_16_1) (and (=> true (and (>= expr_16_1 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_16_1 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_16_1 expr_15_0) (and (=> true (and (>= expr_14_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_14_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_14_0 x_6_1) (and (=> true (and (>= expr_15_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_15_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_15_0 n_11_1) (and (and (>= n_11_1 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= n_11_1 57896044618658097711785492504343953926634992332820282019728792003956564819967)) true))))))))) true) (block_18_return_function_set__19_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 n_11_0 state_1 x_6_2 d_9_1 n_11_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_18_return_function_set__19_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 n_11_0 state_1 x_6_1 d_9_1 n_11_1) true) true) (summary_8_function_set__19_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 n_11_0 state_1 x_6_1 d_9_1 n_11_1))))


(declare-fun |block_19_function_set__19_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(block_19_function_set__19_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 n_11_0 state_1 x_6_1 d_9_1 n_11_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_19_function_set__19_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 n_11_0 state_1 x_6_1 d_9_1 n_11_1) (and (summary_8_function_set__19_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_6_1 d_9_1 n_11_1 state_3 x_6_2 d_9_2 n_11_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3854670637)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 229)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 193)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 45)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_6_1 x_6_0)) (= d_9_1 d_9_0))) (and true (= n_11_1 n_11_0))) true))))))) true) (summary_9_function_set__19_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 n_11_0 state_3 x_6_2 d_9_2 n_11_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (interface_5_C_54_0 this_0 abi_0 crypto_0 state_0 x_6_0 d_9_0) true) (and (summary_9_function_set__19_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 n_11_0 state_1 x_6_1 d_9_1 n_11_1) (= error_0 0))) (interface_5_C_54_0 this_0 abi_0 crypto_0 state_1 x_6_1 d_9_1))))


(declare-fun |block_20_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_21_f_52_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(block_20_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_20_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_6_1 x_6_0)) (= d_9_1 d_9_0))) true) true)) true) (block_21_f_52_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1))))


(declare-fun |block_22_return_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_23_try_header_f_51_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_24_f_52_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_25_try_clause_36f_36_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_26_try_clause_50f_50_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_21_f_52_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (and (= x_6_2 expr_24_1) (and (=> true (and (>= expr_24_1 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_24_1 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_24_1 expr_23_0) (and (=> true (and (>= expr_22_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_22_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_22_0 x_6_1) (and (=> true true) (and (= expr_23_0 0) true)))))))) true) (block_23_try_header_f_51_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_2 d_9_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_23_try_header_f_51_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (and (=> true true) (and (= expr_26_0 d_9_1) true))) true) (block_26_try_clause_50f_50_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1))))


(declare-fun |nondet_call_27_0| (Int Int |abi_type| |crypto_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (nondet_interface_6_C_54_0 error_1 this_0 abi_0 crypto_0 state_1 x_6_1 d_9_1 state_2 x_6_2 d_9_2) (nondet_call_27_0 error_1 this_0 abi_0 crypto_0 state_1 x_6_1 d_9_1 state_2 x_6_2 d_9_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_23_try_header_f_51_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (and (nondet_call_27_0 error_1 this_0 abi_0 crypto_0 state_1 x_6_1 d_9_1 state_2 x_6_2 d_9_2) (and (=> true true) (and (= expr_26_0 d_9_1) true)))) (> error_1 0)) (summary_10_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_2 x_6_2 d_9_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_23_try_header_f_51_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (and (= error_1 0) (and (nondet_call_27_0 error_1 this_0 abi_0 crypto_0 state_1 x_6_1 d_9_1 state_2 x_6_2 d_9_2) (and (=> true true) (and (= expr_26_0 d_9_1) true))))) true) (block_25_try_clause_36f_36_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_2 x_6_2 d_9_2))))


(declare-fun |block_28_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_25_try_clause_36f_36_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (and (= expr_32_1 (= expr_30_0 expr_31_0)) (and (=> true true) (and (= expr_31_0 0) (and (=> true (and (>= expr_30_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_30_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_30_0 x_6_1) true)))))) (and (not expr_32_1) (= error_1 1))) (block_28_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (block_28_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (summary_10_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_25_try_clause_36f_36_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (and (= error_1 error_0) (and (= expr_32_1 (= expr_30_0 expr_31_0)) (and (=> true true) (and (= expr_31_0 0) (and (=> true (and (>= expr_30_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_30_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_30_0 x_6_1) true))))))) true) (block_24_f_52_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1))))


(declare-fun |block_29_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_26_try_clause_50f_50_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (and (= expr_40_1 (= expr_38_0 expr_39_0)) (and (=> true true) (and (= expr_39_0 0) (and (=> true (and (>= expr_38_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_38_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_38_0 x_6_1) true)))))) (and (not expr_40_1) (= error_1 2))) (block_29_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (block_29_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (summary_10_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1))))


(declare-fun |block_30_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_26_try_clause_50f_50_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (and (= expr_46_1 (= expr_44_0 expr_45_0)) (and (=> true true) (and (= expr_45_0 1) (and (=> true (and (>= expr_44_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_44_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_44_0 x_6_1) (and (= error_1 error_0) (and (= expr_40_1 (= expr_38_0 expr_39_0)) (and (=> true true) (and (= expr_39_0 0) (and (=> true (and (>= expr_38_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_38_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_38_0 x_6_1) true)))))))))))) (and (not expr_46_1) (= error_2 3))) (block_30_function_f__53_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (block_30_function_f__53_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (summary_10_function_f__53_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_26_try_clause_50f_50_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (and (= error_2 error_1) (and (= expr_46_1 (= expr_44_0 expr_45_0)) (and (=> true true) (and (= expr_45_0 1) (and (=> true (and (>= expr_44_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_44_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_44_0 x_6_1) (and (= error_1 error_0) (and (= expr_40_1 (= expr_38_0 expr_39_0)) (and (=> true true) (and (= expr_39_0 0) (and (=> true (and (>= expr_38_0 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)) (<= expr_38_0 57896044618658097711785492504343953926634992332820282019728792003956564819967))) (and (= expr_38_0 x_6_1) true))))))))))))) true) (block_24_f_52_54_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_24_f_52_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) true) true) (block_22_return_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_22_return_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) true) true) (summary_10_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1))))


(declare-fun |block_31_function_f__53_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(block_31_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (funds_4_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (block_31_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (and (summary_10_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_6_1 d_9_1 state_3 x_6_2 d_9_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_4_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_4_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_4_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_4_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_6_1 x_6_0)) (= d_9_1 d_9_0))) true) true))))))) true) (summary_11_function_f__53_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_3 x_6_2 d_9_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (funds_4_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (interface_5_C_54_0 this_0 abi_0 crypto_0 state_0 x_6_0 d_9_0) true) (and (summary_11_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (= error_0 0))) (interface_5_C_54_0 this_0 abi_0 crypto_0 state_1 x_6_1 d_9_1))))


(declare-fun |contract_initializer_32_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_33_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (funds_4_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_6_1 x_6_0)) (= d_9_1 d_9_0))) (contract_initializer_entry_33_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_6_0 d_9_0 x_6_1 d_9_1))))


(declare-fun |contract_initializer_after_init_34_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (funds_4_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (contract_initializer_entry_33_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_6_0 d_9_0 x_6_1 d_9_1) true) true) (contract_initializer_after_init_34_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_6_0 d_9_0 x_6_1 d_9_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (funds_4_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (contract_initializer_after_init_34_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_6_0 d_9_0 x_6_1 d_9_1) true) true) (contract_initializer_32_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_6_0 d_9_0 x_6_1 d_9_1))))


(declare-fun |implicit_constructor_entry_35_C_54_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (funds_4_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= x_6_1 x_6_0)) (= d_9_1 d_9_0))) (and (and true (= x_6_1 0)) (= d_9_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_35_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_6_0 d_9_0 x_6_1 d_9_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (funds_4_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (implicit_constructor_entry_35_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_6_0 d_9_0 x_6_1 d_9_1) (and (contract_initializer_32_C_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_6_1 d_9_1 x_6_2 d_9_2) true)) (> error_1 0)) (summary_constructor_7_C_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_6_0 d_9_0 x_6_2 d_9_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (funds_4_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (implicit_constructor_entry_35_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_6_0 d_9_0 x_6_1 d_9_1) (and (= error_1 0) (and (contract_initializer_32_C_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_6_1 d_9_1 x_6_2 d_9_2) true))) true) (summary_constructor_7_C_54_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_6_0 d_9_0 x_6_2 d_9_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (funds_4_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (summary_constructor_7_C_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_6_0 d_9_0 x_6_1 d_9_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_5_C_54_0 this_0 abi_0 crypto_0 state_1 x_6_1 d_9_1))))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (funds_4_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> (and (and (interface_5_C_54_0 this_0 abi_0 crypto_0 state_0 x_6_0 d_9_0) true) (and (summary_11_function_f__53_54_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_6_0 d_9_0 state_1 x_6_1 d_9_1) (= error_0 1))) error_target_5_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_9_0 Int) (d_9_1 Int) (d_9_2 Int) (d_9_3 Int) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_15_0 Int) (expr_16_1 Int) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Int) (expr_26_0 Int) (expr_28_1 |tuple()|) (expr_30_0 Int) (expr_31_0 Int) (expr_32_1 Bool) (expr_38_0 Int) (expr_39_0 Int) (expr_40_1 Bool) (expr_44_0 Int) (expr_45_0 Int) (expr_46_1 Bool) (funds_0_0 Int) (funds_4_0 Int) (n_11_0 Int) (n_11_1 Int) (n_11_2 Int) (n_11_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_6_0 Int) (x_6_1 Int) (x_6_2 Int) (x_6_3 Int))
(=> error_target_5_0 false)))
(check-sat)