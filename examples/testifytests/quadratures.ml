type qk_result =
  { result: float
  ; (* approximation to the integral of [f] *)
    abserr: float
  ; (* estimate of the modulus of the absolute error, which should not exceed
       abs(i-result) *)
    i: float
        (* ; resabs: float
         * ; (\* approximation to the integral of [abs f] *\)
         *   resasc: float (\* approximation to the integral of abs(f-i/(b-a)) *\) *)
  }

(* [@@s.t
 *   resabs >=. 0. && resasc >=. 0.
 *   && ( (abserr <=. i -. result && i >=. result)
 *      || (abserr <=. result -. i && i <. result) )] *)
