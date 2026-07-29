@k("")
permit(
  principal,
  action == L::V::QN::n::Action::"action",
  resource == L::V::QN::n::A::"\0\0"
) when {
  ((true && (((L::V::QN::n::A::"\0\0".h).h) in ((L::V::QN::n::A::"\0\0".h).h))) && (((L::V::QN::n::A::"\0\0".h).h) in L::V::QN::n::A::"\0\0")) && true
};
