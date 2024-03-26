;;! target = "s390x"
;;! test = "compile"
;;! flags = " -C cranelift-enable-heap-access-spectre-mitigation -O static-memory-maximum-size=0 -O static-memory-guard-size=0 -O dynamic-memory-guard-size=0"

;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
;; !!! GENERATED BY 'make-load-store-tests.sh' DO NOT EDIT !!!
;; !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

(module
  (memory i32 1)

  (func (export "do_store") (param i32 i32)
    local.get 0
    local.get 1
    i32.store8 offset=0xffff0000)

  (func (export "do_load") (param i32) (result i32)
    local.get 0
    i32.load8_u offset=0xffff0000))

;; wasm[0]::function[0]:
;;    0: stmg    %r6, %r15, 0x30(%r15)
;;    6: lgr     %r1, %r15
;;    a: aghi    %r15, -0xa0
;;    e: stg     %r1, 0(%r15)
;;   14: lgr     %r11, %r2
;;   18: llgfr   %r3, %r4
;;   1c: llilf   %r2, 0xffff0001
;;   22: algfr   %r2, %r4
;;   26: jgnle   0x28
;;   2c: lgr     %r6, %r11
;;   30: lg      %r11, 0x58(%r6)
;;   36: lghi    %r4, 0
;;   3a: ag      %r3, 0x50(%r6)
;;   40: llilh   %r12, 0xffff
;;   44: agr     %r3, %r12
;;   48: clgr    %r2, %r11
;;   4c: locgrh  %r3, %r4
;;   50: stc     %r5, 0(%r3)
;;   54: lmg     %r6, %r15, 0xd0(%r15)
;;   5a: br      %r14
;;
;; wasm[0]::function[1]:
;;   5c: stmg    %r6, %r15, 0x30(%r15)
;;   62: lgr     %r1, %r15
;;   66: aghi    %r15, -0xa0
;;   6a: stg     %r1, 0(%r15)
;;   70: lgr     %r5, %r2
;;   74: llgfr   %r3, %r4
;;   78: llilf   %r2, 0xffff0001
;;   7e: algfr   %r2, %r4
;;   82: jgnle   0x84
;;   88: lgr     %r6, %r5
;;   8c: lg      %r5, 0x58(%r6)
;;   92: lghi    %r4, 0
;;   96: ag      %r3, 0x50(%r6)
;;   9c: llilh   %r11, 0xffff
;;   a0: agr     %r3, %r11
;;   a4: clgr    %r2, %r5
;;   a8: locgrh  %r3, %r4
;;   ac: llc     %r2, 0(%r3)
;;   b2: lmg     %r6, %r15, 0xd0(%r15)
;;   b8: br      %r14
