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
    i32.store offset=0x1000)

  (func (export "do_load") (param i32) (result i32)
    local.get 0
    i32.load offset=0x1000))

;; wasm[0]::function[0]:
;;    0: stmg    %r14, %r15, 0x70(%r15)
;;    6: lgr     %r1, %r15
;;    a: aghi    %r15, -0xa0
;;    e: stg     %r1, 0(%r15)
;;   14: lgr     %r3, %r4
;;   18: lg      %r4, 0x58(%r2)
;;   1e: llgfr   %r3, %r3
;;   22: aghi    %r4, -0x1004
;;   26: clgr    %r3, %r4
;;   2a: jgh     0x48
;;   30: ag      %r3, 0x50(%r2)
;;   36: lghi    %r2, 0x1000
;;   3a: strv    %r5, 0(%r2, %r3)
;;   40: lmg     %r14, %r15, 0x110(%r15)
;;   46: br      %r14
;;   48: .byte   0x00, 0x00
;;
;; wasm[0]::function[1]:
;;   4c: stmg    %r14, %r15, 0x70(%r15)
;;   52: lgr     %r1, %r15
;;   56: aghi    %r15, -0xa0
;;   5a: stg     %r1, 0(%r15)
;;   60: lg      %r3, 0x58(%r2)
;;   66: llgfr   %r5, %r4
;;   6a: aghi    %r3, -0x1004
;;   6e: clgr    %r5, %r3
;;   72: jgh     0x90
;;   78: ag      %r5, 0x50(%r2)
;;   7e: lghi    %r2, 0x1000
;;   82: lrv     %r2, 0(%r2, %r5)
;;   88: lmg     %r14, %r15, 0x110(%r15)
;;   8e: br      %r14
;;   90: .byte   0x00, 0x00
