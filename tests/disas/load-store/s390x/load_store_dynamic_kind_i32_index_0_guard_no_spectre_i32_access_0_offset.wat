;;! target = "s390x"
;;! test = "compile"
;;! flags = " -C cranelift-enable-heap-access-spectre-mitigation=false -O static-memory-maximum-size=0 -O static-memory-guard-size=0 -O dynamic-memory-guard-size=0"

;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
;; !!! GENERATED BY 'make-load-store-tests.sh' DO NOT EDIT !!!
;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

(module
  (memory i32 1)

  (func (export "do_store") (param i32 i32)
    local.get 0
    local.get 1
    i32.store offset=0)

  (func (export "do_load") (param i32) (result i32)
    local.get 0
    i32.load offset=0))

;; wasm[0]::function[0]:
;;    0: stmg    %r14, %r15, 0x70(%r15)
;;    6: lgr     %r1, %r15
;;    a: aghi    %r15, -0xa0
;;    e: stg     %r1, 0(%r15)
;;   14: lgr     %r3, %r4
;;   18: lg      %r4, 0x58(%r2)
;;   1e: llgfr   %r3, %r3
;;   22: aghi    %r4, -4
;;   26: clgr    %r3, %r4
;;   2a: jgh     0x44
;;   30: lg      %r4, 0x50(%r2)
;;   36: strv    %r5, 0(%r3, %r4)
;;   3c: lmg     %r14, %r15, 0x110(%r15)
;;   42: br      %r14
;;   44: .byte   0x00, 0x00
;;
;; wasm[0]::function[1]:
;;   48: stmg    %r14, %r15, 0x70(%r15)
;;   4e: lgr     %r1, %r15
;;   52: aghi    %r15, -0xa0
;;   56: stg     %r1, 0(%r15)
;;   5c: lgr     %r5, %r4
;;   60: lg      %r4, 0x58(%r2)
;;   66: llgfr   %r3, %r5
;;   6a: aghi    %r4, -4
;;   6e: clgr    %r3, %r4
;;   72: jgh     0x8c
;;   78: lg      %r4, 0x50(%r2)
;;   7e: lrv     %r2, 0(%r3, %r4)
;;   84: lmg     %r14, %r15, 0x110(%r15)
;;   8a: br      %r14
;;   8c: .byte   0x00, 0x00
