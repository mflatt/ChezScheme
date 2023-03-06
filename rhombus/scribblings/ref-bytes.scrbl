#lang scribble/rhombus/manual
@(import: "common.rhm" open)

@title{Byte Strings}

A @deftech{byte string} is a sequence of bytes (i.e., integers between 0
and 255 inclusive). A byte string works with map-referencing @brackets
to access a byte via @rhombus(#%ref). A byte string also works with the
@rhombus(++) operator to append bytes strings. A byte string can be used
as @tech{sequence}, in which case it supplies its bytes in order.

@dispatch_table(
  "byte string"
  @rhombus(Bytes)
  [bstr.length(), Bytes.length(bstr)]
  [bstr.subbytes(arg, ...), Bytes.subbytes(bstr, arg, ...)]
  [bstr.utf8_string(arg, ...), Bytes.utf8_string(bstr, arg, ...)]
  [bstr.latin1_string(arg, ...), Bytes.latin1_string(bstr, arg, ...)]
  [bstr.locale_string(arg, ...), Bytes.locale_string(bstr, arg, ...)]
)


@doc(
  annot.macro 'Bytes'
){

  Matches byte strings.

}


@doc(
  fun Bytes.length(bstr :: Bytes) :: NonnegInt
){

 Returns the number of bytes in @rhombus(bstr).

@examples(
  Bytes.length(#"hello")
  #"hello".length()
)

}


@doc(
  fun Bytes.subbytes(bstr :: Bytes,
                     start :: NonnegInt,
                     end :: NonnegInt = Bytes.length(str)) :: Bytes
){

 Returns the substring of @rhombus(bstr) from @rhombus(start) (inclusive)
 to @rhombus(end) (exclusive).

@examples(
  Bytes.subbytes(#"hello", 2, 4)
  Bytes.subbytes(#"hello", 2)
)

}

@doc(
  fun Bytes.utf8_string(bstr :: Bytes,
                        err_char :: Optional[Char] = #false,
                        start :: NonnegInt = 0,
                        end :: NonnegInt = Bytes.length(bstr)) :: String
  fun Bytes.latin1_string(bstr :: Bytes,
                          err_char :: Optional[Char] = #false,
                          start :: NonnegInt = 0,
                          end :: NonnegInt = Bytes.length(bstr)) :: Bytes
  fun Bytes.locale_string(str :: String,
                          err_char :: Optional[Char] = #false,
                          start :: NonnegInt = 0,
                          end :: NonnegInt = Bytes.length(bstr)) :: Bytes
){

 Converts a byte string to a string, decoding as UTF-8, Latin-1, or the
 current locale's encoding. The @rhombus(err_char) argument provides a
 @tech{character} to use in place of an encoding error, where
 @rhombus(#false) means that an exception is raised.

@examples(
  #"hello".utf8_string()
)

}

