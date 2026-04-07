pub type DResult<T> = Result<T, DocError>;

#[derive(Debug)]
pub enum DocError {
    FWriteError,
}
