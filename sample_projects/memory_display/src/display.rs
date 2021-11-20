enum DisplayState {
    // Unitialised and has been for x cycles
    Uninit(duration: int<16>),
    // Currently transmitting the header for the start of a line
    TransmitLineHeader(line: int<8>),
    // Currently transmitting the pixels of line `line`. The pixels being transmitted are
    // col..col+8
    TransmitPixels(line: int<8>, col: int<8>),
    // Transmitting the padding betwene lines
    InterLinePadding(line: int<8>),
    // Transmitting the end of frame padding and have been doing so for `duration`
    // spi frames
    EndOfFramePadding(duration: int<2>),
    // Keeping chip select high until display is ready
    EndOfFrameWait(int<8>)
}
