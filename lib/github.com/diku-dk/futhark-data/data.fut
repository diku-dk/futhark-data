-- | Reading and writing binary Futhark data files.
--
-- This file provides facilities for reading and writing byte streams
-- representing values in the Futhark binary data format, which is accepted by
-- most Futhark tooling. See the Futhark compiler documentation for details
-- about this format.
--
-- The functions provided here provide little in the way of error detection and
-- largely assume correct input. Do not use `#[unsafe]` with these functions in
-- the presence of untrusted input.
--
-- The `next` functions read a value and also provide the bytes following the
-- value. The `decode` functions simply discard the remainder. Both abort with a
-- failed assertion on invalid input.

-- | Primitive element type.
type prim =
    #i8
  | #i16
  | #i32
  | #i64
  | #u8
  | #u16
  | #u32
  | #u64
  | #f16
  | #f32
  | #f64
  | #bool

-- | The four-byte identifying string for a primitive type.
def prim_id (t: prim) : [4]u8 =
  match t
  case #i8 -> "  i8"
  case #i16 -> " i16"
  case #i32 -> " i32"
  case #i64 -> " i64"
  case #u8 -> "  u8"
  case #u16 -> " u16"
  case #u32 -> " u32"
  case #u64 -> " u64"
  case #f16 -> " f16"
  case #f32 -> " f32"
  case #f64 -> " f64"
  case #bool -> "bool"

-- | The primitive type corresponding to this identifying string.
def id_prim (s: [4]u8) : #some prim | #none =
  let eq x = x[0] == s[0] && x[1] == s[1] && x[2] == s[2] && x[3] == s[3]
  in if eq (prim_id #i8)
     then #some #i8
     else if eq (prim_id #i16)
     then #some #i16
     else if eq (prim_id #i32)
     then #some #i32
     else if eq (prim_id #i64)
     then #some #i64
     else if eq (prim_id #u8)
     then #some #u8
     else if eq (prim_id #u16)
     then #some #u16
     else if eq (prim_id #u32)
     then #some #u32
     else if eq (prim_id #u64)
     then #some #i64
     else if eq (prim_id #f16)
     then #some #f16
     else if eq (prim_id #f32)
     then #some #f32
     else if eq (prim_id #f64)
     then #some #i64
     else if eq (prim_id #bool)
     then #some #bool
     else #none

-- | The size in bytes of a primitive value of this type.
def prim_size (t: prim) : i64 =
  match t
  case #i8 -> 1
  case #i16 -> 2
  case #i32 -> 4
  case #i64 -> 8
  case #u8 -> 1
  case #u16 -> 2
  case #u32 -> 4
  case #u64 -> 8
  case #f16 -> 2
  case #f32 -> 4
  case #f64 -> 8
  case #bool -> 1

-- | A rank-`k` value with a total of `m` elements. The product of the shape
-- equals `m`.
type value [k] [m] 't = {shape: [k]i64, vals: [m]t}

local
def bytes_to_i64 (bs: [8]u8) : i64 =
  loop x = 0 for i < 8 do x + (i64.u8 bs[i] << (i * 8))

local
def bytes_to_i32 (bs: [4]u8) : i32 =
  loop x = 0 for i < 4 do x + (i32.u8 bs[i] << (i * 8))

local
def bytes_to_i16 (bs: [2]u8) : i16 =
  loop x = 0 for i < 2 do x + (i16.u8 bs[i] << (i * 8))

local
def bytes_to_u64 (bs: [8]u8) : u64 =
  u64.i64 (bytes_to_i64 bs)

local
def bytes_to_u32 (bs: [4]u8) : u32 =
  u32.i32 (bytes_to_i32 bs)

local
def bytes_to_u16 (bs: [2]u8) : u16 =
  u16.i16 (bytes_to_i16 bs)

local
def i64_to_bytes (x: i64) : [8]u8 =
  [ u8.i64 (x >> 0)
  , u8.i64 (x >> 8)
  , u8.i64 (x >> 16)
  , u8.i64 (x >> 24)
  , u8.i64 (x >> 32)
  , u8.i64 (x >> 40)
  , u8.i64 (x >> 48)
  , u8.i64 (x >> 56)
  ]

local
def i32_to_bytes (x: i32) : [4]u8 =
  [ u8.i32 (x >> 0)
  , u8.i32 (x >> 8)
  , u8.i32 (x >> 16)
  , u8.i32 (x >> 24)
  ]

local
def i16_to_bytes (x: i16) : [2]u8 =
  [ u8.i16 (x >> 0)
  , u8.i16 (x >> 8)
  ]

local
def u64_to_bytes (x: u64) : [8]u8 =
  [ u8.u64 (x >> 0)
  , u8.u64 (x >> 8)
  , u8.u64 (x >> 16)
  , u8.u64 (x >> 24)
  , u8.u64 (x >> 32)
  , u8.u64 (x >> 40)
  , u8.u64 (x >> 48)
  , u8.u64 (x >> 56)
  ]

local
def u32_to_bytes (x: u32) : [4]u8 =
  [ u8.u32 (x >> 0)
  , u8.u32 (x >> 8)
  , u8.u32 (x >> 16)
  , u8.u32 (x >> 24)
  ]

local
def u16_to_bytes (x: u16) : [2]u8 =
  [ u8.u16 (x >> 0)
  , u8.u16 (x >> 8)
  ]

local
def decode_header [n] (s: [n]u8) =
  let b = s[0]
  let v = s[1]
  let k = i64.u8 s[2]
  let id = take 4 s[3:]
  in (b, v, k, id)

local
def next_generic [n] [p] 't (to_t: [p]u8 -> t) (s: [n]u8) : ?[k][m][n'].(value [k] [m] t, [n']u8) =
  let (b, v, k, _id) = decode_header s
  let shape = drop 7 s |> take (k * 8) |> unflatten |> map bytes_to_i64
  let m = i64.product shape
  let vals =
    assert (b == 'b' && v == 1)
    s
    |> drop (7 * k + 8)
    |> take (m * p)
    |> unflatten
    |> map to_t
  in ({shape, vals}, drop (7 * k + 8 + m * p) s)

def next_bool [n] : [n]u8 -> ?[k][m][n'].(value [k] [m] bool, [n']u8) =
  next_generic (\(b: [1]u8) -> bool.u8 b[0])

def next_i8 [n] : [n]u8 -> ?[k][m][n'].(value [k] [m] i8, [n']u8) =
  next_generic (\(b: [1]u8) -> i8.u8 b[0])

def next_i16 [n] : [n]u8 -> ?[k][m][n'].(value [k] [m] i16, [n']u8) =
  next_generic bytes_to_i16

def next_i32 [n] : [n]u8 -> ?[k][m][n'].(value [k] [m] i32, [n']u8) =
  next_generic bytes_to_i32

def next_i64 [n] : [n]u8 -> ?[k][m][n'].(value [k] [m] i64, [n']u8) =
  next_generic bytes_to_i64

def next_u8 [n] : [n]u8 -> ?[k][m][n'].(value [k] [m] u8, [n']u8) =
  next_generic (\(b: [1]u8) -> b[0])

def next_u16 [n] : [n]u8 -> ?[k][m][n'].(value [k] [m] u16, [n']u8) =
  next_generic bytes_to_u16

def next_u32 [n] : [n]u8 -> ?[k][m][n'].(value [k] [m] u32, [n']u8) =
  next_generic bytes_to_u32

def next_u64 [n] : [n]u8 -> ?[k][m][n'].(value [k] [m] u64, [n']u8) =
  next_generic bytes_to_u64

def next_f16 [n] : [n]u8 -> ?[k][m][n'].(value [k] [m] f16, [n']u8) =
  next_generic (bytes_to_u16 >-> f16.from_bits)

def next_f32 [n] : [n]u8 -> ?[k][m][n'].(value [k] [m] f32, [n']u8) =
  next_generic (bytes_to_u32 >-> f32.from_bits)

def next_f64 [n] : [n]u8 -> ?[k][m][n'].(value [k] [m] f64, [n']u8) =
  next_generic (bytes_to_u64 >-> f64.from_bits)

local
def decode_generic [n] [p] 't (to_t: [p]u8 -> t) (s: [n]u8) : ?[k][m].(value [k] [m] t) =
  (next_generic to_t s).0

def decode_bool [n] (s: [n]u8) : ?[k][m].value [k] [m] bool =
  (next_bool s).0

def decode_i8 [n] (s: [n]u8) : ?[k][m].value [k] [m] i8 =
  (next_i8 s).0

def decode_i16 [n] : [n]u8 -> ?[k][m].value [k] [m] i16 =
  decode_generic bytes_to_i16

def decode_i32 [n] : [n]u8 -> ?[k][m].value [k] [m] i32 =
  decode_generic bytes_to_i32

def decode_i64 [n] : [n]u8 -> ?[k][m].value [k] [m] i64 =
  decode_generic bytes_to_i64

def decode_u8 [n] : [n]u8 -> ?[k][m].value [k] [m] u8 =
  decode_generic (\(b: [1]u8) -> b[0])

def decode_u16 [n] : [n]u8 -> ?[k][m].value [k] [m] u16 =
  decode_generic bytes_to_u16

def decode_u32 [n] : [n]u8 -> ?[k][m].value [k] [m] u32 =
  decode_generic bytes_to_u32

def decode_u64 [n] : [n]u8 -> ?[k][m].value [k] [m] u64 =
  decode_generic bytes_to_u64

def decode_f16 [n] : [n]u8 -> ?[k][m].value [k] [m] f16 =
  decode_generic (bytes_to_u16 >-> f16.from_bits)

def decode_f32 [n] : [n]u8 -> ?[k][m].value [k] [m] f32 =
  decode_generic (bytes_to_u32 >-> f32.from_bits)

def decode_f64 [n] : [n]u8 -> ?[k][m].value [k] [m] f64 =
  decode_generic (bytes_to_u64 >-> f64.from_bits)

local
def encode_generic [k] [m] [p] 't (pt: prim) (to_bytes: t -> [p]u8) (v: value [k] [m] t) : ?[n].[n]u8 =
  ['b', 1, u8.i64 k]
  ++ prim_id pt
  ++ flatten (map i64_to_bytes v.shape)
  ++ flatten (map to_bytes v.vals)

def encode_bool [k] [m] : value [k] [m] bool -> ?[n].[n]u8 =
  encode_generic #bool (\x -> [u8.bool x])

def encode_i8 [k] [m] : value [k] [m] i8 -> ?[n].[n]u8 =
  encode_generic #i8 (\x -> [u8.i8 x])

def encode_i16 [k] [m] : value [k] [m] i16 -> ?[n].[n]u8 =
  encode_generic #i16 i16_to_bytes

def encode_i32 [k] [m] : value [k] [m] i32 -> ?[n].[n]u8 =
  encode_generic #i32 i32_to_bytes

def encode_i64 [k] [m] : value [k] [m] i64 -> ?[n].[n]u8 =
  encode_generic #i64 i64_to_bytes

def encode_u8 [k] [m] : value [k] [m] u8 -> ?[n].[n]u8 =
  encode_generic #u8 (\x -> [x])

def encode_u16 [k] [m] : value [k] [m] u16 -> ?[n].[n]u8 =
  encode_generic #u16 u16_to_bytes

def encode_u32 [k] [m] : value [k] [m] u32 -> ?[n].[n]u8 =
  encode_generic #u32 u32_to_bytes

def encode_u64 [k] [m] : value [k] [m] u64 -> ?[n].[n]u8 =
  encode_generic #u64 u64_to_bytes

def encode_f16 [k] [m] : value [k] [m] f16 -> ?[n].[n]u8 =
  encode_generic #f16 (f16.to_bits >-> u16_to_bytes)

def encode_f32 [k] [m] : value [k] [m] f32 -> ?[n].[n]u8 =
  encode_generic #f32 (f32.to_bits >-> u32_to_bytes)

def encode_f64 [k] [m] : value [k] [m] f64 -> ?[n].[n]u8 =
  encode_generic #f64 (f64.to_bits >-> u64_to_bytes)
