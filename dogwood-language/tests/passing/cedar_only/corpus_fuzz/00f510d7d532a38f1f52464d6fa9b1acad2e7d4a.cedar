permit(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  (true && ({"\0~}]": false} == context)) && false
};
