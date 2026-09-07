// top=cxx::top::fields

#include <cassert>
#define TOP fields

#include <verilator_util.hpp>

TEST_CASE(it_works, {
    dut->eval();
    ctx->timeInc(1);
    dut->eval();

    s.i->a = "5";
    s.i->b = "10";
    s.i->c = "20";

    ctx->timeInc(1);
    dut->eval();

    ctx->timeInc(1);
    dut->eval();

    ASSERT_EQ(s.o, "FieldOut { a: 5, sub: FieldOutSub { b: 10, c: 20 } }");
    ASSERT_EQ(s.o->a, "5");
    ASSERT_EQ(s.o->sub, "FieldOutSub { b: 10, c: 20 }");
    ASSERT_EQ(s.o->sub->b, "10");
    ASSERT_EQ(s.o->sub->c, "20");
    return 0;
})

MAIN
