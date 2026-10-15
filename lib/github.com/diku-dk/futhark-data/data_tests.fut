-- | ignore

-- ==
-- property: bool_encode_read i8_encode_read i16_encode_read i32_encode_read i64_encode_read u8_encode_read u16_encode_read u32_encode_read u64_encode_read f16_encode_read f32_encode_read f64_encode_read

module D = import "data"

def eq_arr 'a [n] [m] (eq: a -> a -> bool) (a: [n]a) (b: [m]a) : bool =
  n == m && and (map2 eq a (b :> [n]a))

def eq_val 't [k1] [k2] [n1] [n2]
           (eq: t -> t -> bool)
           (v1: D.value [k1] [n1] t)
           (v2: D.value [k2] [n2] t) =
  k1 == k2 && n1 == n2
  && eq_arr (==) v1.shape (sized k1 (v2.shape))
  && eq_arr eq v1.vals (sized n1 v2.vals)

entry gen_value_bool (size: i64) (seed: u64) : D.value [] [] bool =
  let vals = tabulate size \i -> bool.i64 ((i ^ i64.u64 seed) % 2)
  let shape = [size]
  in {shape, vals}

entry gen_value_i8 (size: i64) (seed: u64) : D.value [] [] i8 =
  let vals = tabulate size \i -> i8.i64 (i ^ i64.u64 seed)
  let shape = [size]
  in {shape, vals}

entry gen_value_i16 (size: i64) (seed: u64) : D.value [] [] i16 =
  let vals = tabulate size \i -> i16.i64 (i ^ i64.u64 seed)
  let shape = [size]
  in {shape, vals}

entry gen_value_i32 (size: i64) (seed: u64) : D.value [] [] i32 =
  let vals = tabulate size \i -> i32.i64 (i ^ i64.u64 seed)
  let shape = [size]
  in {shape, vals}

entry gen_value_i64 (size: i64) (seed: u64) : D.value [] [] i64 =
  let vals = tabulate size \i -> (i ^ i64.u64 seed)
  let shape = [size]
  in {shape, vals}

entry gen_value_u8 (size: i64) (seed: u64) : D.value [] [] u8 =
  let {shape, vals} = gen_value_i8 size seed
  in {shape, vals = map u8.i8 vals}

entry gen_value_u16 (size: i64) (seed: u64) : D.value [] [] u16 =
  let {shape, vals} = gen_value_i16 size seed
  in {shape, vals = map u16.i16 vals}

entry gen_value_u32 (size: i64) (seed: u64) : D.value [] [] u32 =
  let {shape, vals} = gen_value_i32 size seed
  in {shape, vals = map u32.i32 vals}

entry gen_value_u64 (size: i64) (seed: u64) : D.value [] [] u64 =
  let {shape, vals} = gen_value_i64 size seed
  in {shape, vals = map u64.i64 vals}

entry gen_value_f16 (size: i64) (seed: u64) : D.value [] [] f16 =
  let {shape, vals} = gen_value_u16 size seed
  in {shape, vals = map f16.from_bits vals}

entry gen_value_f32 (size: i64) (seed: u64) : D.value [] [] f32 =
  let {shape, vals} = gen_value_u32 size seed
  in {shape, vals = map f32.from_bits vals}

entry gen_value_f64 (size: i64) (seed: u64) : D.value [] [] f64 =
  let {shape, vals} = gen_value_u64 size seed
  in {shape, vals = map f64.from_bits vals}

#[prop(gen(gen_value_bool))]
entry bool_encode_read (v: D.value [] [] bool) =
  eq_val (==) v (D.decode_bool (D.encode_bool v))

#[prop(gen(gen_value_i8))]
entry i8_encode_read (v: D.value [] [] i8) =
  eq_val (==) v (D.decode_i8 (D.encode_i8 v))

#[prop(gen(gen_value_i16))]
entry i16_encode_read (v: D.value [] [] i16) =
  eq_val (==) v (D.decode_i16 (D.encode_i16 v))

#[prop(gen(gen_value_i32))]
entry i32_encode_read (v: D.value [] [] i32) =
  eq_val (==) v (D.decode_i32 (D.encode_i32 v))

#[prop(gen(gen_value_i64))]
entry i64_encode_read (v: D.value [] [] i64) =
  eq_val (==) v (D.decode_i64 (D.encode_i64 v))

#[prop(gen(gen_value_u8))]
entry u8_encode_read (v: D.value [] [] u8) =
  eq_val (==) v (D.decode_u8 (D.encode_u8 v))

#[prop(gen(gen_value_u16))]
entry u16_encode_read (v: D.value [] [] u16) =
  eq_val (==) v (D.decode_u16 (D.encode_u16 v))

#[prop(gen(gen_value_u32))]
entry u32_encode_read (v: D.value [] [] u32) =
  eq_val (==) v (D.decode_u32 (D.encode_u32 v))

#[prop(gen(gen_value_u64))]
entry u64_encode_read (v: D.value [] [] u64) =
  eq_val (==) v (D.decode_u64 (D.encode_u64 v))

#[prop(gen(gen_value_f16))]
entry f16_encode_read (v: D.value [] [] f16) =
  let f16_eq x y = f16.isnan x && f16.isnan y || x == y
  in eq_val f16_eq v (D.decode_f16 (D.encode_f16 v))

#[prop(gen(gen_value_f32))]
entry f32_encode_read (v: D.value [] [] f32) =
  let f32_eq x y = f32.isnan x && f32.isnan y || x == y
  in eq_val f32_eq v (D.decode_f32 (D.encode_f32 v))

#[prop(gen(gen_value_f64))]
entry f64_encode_read (v: D.value [] [] f64) =
  let f64_eq x y = f64.isnan x && f64.isnan y || x == y
  in eq_val f64_eq v (D.decode_f64 (D.encode_f64 v))
