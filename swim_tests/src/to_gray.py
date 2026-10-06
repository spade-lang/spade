#top = gray_code::to_gray4

from spade import SpadeExt
import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    binary = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    gray = [
      0b0000,
      0b0001,
      0b0011,
      0b0010,
      0b0110,
      0b0111,
      0b0101,
      0b0100,
      0b1100,
      0b1101,
      0b1111,
      0b1110,
      0b1010,
      0b1011,
      0b1001,
      0b1000,
    ]

    for (b, g) in zip(binary, gray):
        s.i.x = f"{b}u";
        await Timer(1, units='ns')
        s.o.assert_eq(f"{g}u")

