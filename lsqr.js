/**
 *
 * This is a Javascript version of LSQR, derived from the Fortran 77 implementation
 * of C++. C. Paige and M. A. Saunders.
 *
 * http://web.stanford.edu/group/SOL/software/lsqr/
 *
 * 08 Sep 1999: First version from James W. Howse <jhowse@lanl.gov>
 * 13 May 2003: Converted to C++ for gcc by J.A. Tomlin
 * 02 Aug 2007: Debugged on Red Hat Linux and tested out OK.
 * 21 Oct 2015: Converted to Javascript by S. Ledesma
  */


/*
 *------------------------------------------------------------------------------
 *
 *     LSQR  finds a solution x to the following problems:
 *
 *     1. Unsymmetric equations --    solve  A*x = b
 *
 *     2. Linear least squares  --    solve  A*x = b
 *                                    in the least-squares sense
 *
 *     3. Damped least squares  --    solve  (   A    )*x = ( b )
 *                                           ( damp*I )     ( 0 )
 *                                    in the least-squares sense
 *
 *     where 'A' is a matrix with 'm' rows and 'n' columns, 'b' is an
 *     'm'-vector, and 'damp' is a scalar.  (All quantities are real.)
 *     The matrix 'A' is intended to be large and sparse.
 *
 *
 *     Notation
 *     --------
 *
 *     The following quantities are used in discussing the subroutine
 *     parameters:
 *
 *     'Abar'   =  (   A    ),          'bbar'  =  ( b )
 *                 ( damp*I )                      ( 0 )
 *
 *     'r'      =  b  -  A*x,           'rbar'  =  bbar  -  Abar*x
 *
 *     'rnorm'  =  sqrt( norm(r)**2  +  damp**2 * norm(x)**2 )
 *              =  norm( rbar )
 *
 *     'rel_prec'  =  the relative precision of floating-point arithmetic
 *                    on the machine being used.  Typically 2.22e-16
 *                    with 64-bit arithmetic.
 *
 *     LSQR  minimizes the function 'rnorm' with respect to 'x'.
 *
 *
 *     References
 *     ----------
 *
 *     C.C. Paige and M.A. Saunders,  LSQR: An algorithm for sparse
 *          linear equations and sparse least squares,
 *          ACM Transactions on Mathematical Software 8, 1 (March 1982),
 *          pp. 43-71.
 *
 *     C.C. Paige and M.A. Saunders,  Algorithm 583, LSQR: Sparse
 *          linear equations and least-squares problems,
 *          ACM Transactions on Mathematical Software 8, 2 (June 1982),
 *          pp. 195-209.
 *
 *     C.L. Lawson, R.J. Hanson, D.R. Kincaid and F.T. Krogh,
 *          Basic linear algebra subprograms for Fortran usage,
 *          ACM Transactions on Mathematical Software 5, 3 (Sept 1979),
 *          pp. 308-323 and 324-325.
 *
 *------------------------------------------------------------------------------
 */


// sprintf function. It should be in a separate module, but for now we put it here
(function () {
    "use strict";

    // sprintf
    (function(){
        var re = {
            not_string: /[^s]/,
            number: /[diefg]/,
            json: /[j]/,
            not_json: /[^j]/,
            text: /^[^\x25]+/,
            modulo: /^\x25{2}/,
            placeholder: /^\x25(?:([1-9]\d*)\$|\(([^\)]+)\))?(\+)?(0|'[^$])?(-)?(\d+)?(?:\.(\d+))?([b-gijosuxX])/,
            key: /^([a-z_][a-z_\d]*)/i,
            key_access: /^\.([a-z_][a-z_\d]*)/i,
            index_access: /^\[(\d+)\]/,
            sign: /^[\+\-]/
        }

        function sprintf() {
            var key = arguments[0], cache = sprintf.cache
            if (!(cache[key] && cache.hasOwnProperty(key))) {
                cache[key] = sprintf.parse(key)
            }
            return sprintf.format.call(null, cache[key], arguments)
        }

        sprintf.format = function (parse_tree, argv) {
            var cursor = 1, tree_length = parse_tree.length, node_type = "", arg, output = [], i, k, match, pad, pad_character, pad_length, is_positive = true, sign = ""
            for (i = 0; i < tree_length; i++) {
                node_type = get_type(parse_tree[i])
                if (node_type === "string") {
                    output[output.length] = parse_tree[i]
                }
                else if (node_type === "array") {
                    match = parse_tree[i] // convenience purposes only
                    if (match[2]) { // keyword argument
                        arg = argv[cursor]
                        for (k = 0; k < match[2].length; k++) {
                            if (!arg.hasOwnProperty(match[2][k])) {
                                throw new Error(sprintf("[sprintf] property '%s' does not exist", match[2][k]))
                            }
                            arg = arg[match[2][k]]
                        }
                    }
                    else if (match[1]) { // positional argument (explicit)
                        arg = argv[match[1]]
                    }
                    else { // positional argument (implicit)
                        arg = argv[cursor++]
                    }

                    if (get_type(arg) == "function") {
                        arg = arg()
                    }

                    if (re.not_string.test(match[8]) && re.not_json.test(match[8]) && (get_type(arg) != "number" && isNaN(arg))) {
                        throw new TypeError(sprintf("[sprintf] expecting number but found %s", get_type(arg)))
                    }

                    if (re.number.test(match[8])) {
                        is_positive = arg >= 0
                    }

                    switch (match[8]) {
                        case "b":
                            arg = arg.toString(2)
                            break
                        case "c":
                            arg = String.fromCharCode(arg)
                            break
                        case "d":
                        case "i":
                            arg = parseInt(arg, 10)
                            break
                        case "j":
                            arg = JSON.stringify(arg, null, match[6] ? parseInt(match[6]) : 0)
                            break
                        case "e":
                            arg = match[7] ? arg.toExponential(match[7]) : arg.toExponential()
                            break
                        case "f":
                            arg = match[7] ? parseFloat(arg).toFixed(match[7]) : parseFloat(arg)
                            break
                        case "g":
                            arg = match[7] ? parseFloat(arg).toPrecision(match[7]) : parseFloat(arg)
                            break
                        case "o":
                            arg = arg.toString(8)
                            break
                        case "s":
                            arg = ((arg = String(arg)) && match[7] ? arg.substring(0, match[7]) : arg)
                            break
                        case "u":
                            arg = arg >>> 0
                            break
                        case "x":
                            arg = arg.toString(16)
                            break
                        case "X":
                            arg = arg.toString(16).toUpperCase()
                            break
                    }
                    if (re.json.test(match[8])) {
                        output[output.length] = arg
                    }
                    else {
                        if (re.number.test(match[8]) && (!is_positive || match[3])) {
                            sign = is_positive ? "+" : "-"
                            arg = arg.toString().replace(re.sign, "")
                        }
                        else {
                            sign = ""
                        }
                        pad_character = match[4] ? match[4] === "0" ? "0" : match[4].charAt(1) : " "
                        pad_length = match[6] - (sign + arg).length
                        pad = match[6] ? (pad_length > 0 ? str_repeat(pad_character, pad_length) : "") : ""
                        output[output.length] = match[5] ? sign + arg + pad : (pad_character === "0" ? sign + pad + arg : pad + sign + arg)
                    }
                }
            }
            return output.join("")
        }

        sprintf.cache = {}

        sprintf.parse = function (fmt) {
            var _fmt = fmt, match = [], parse_tree = [], arg_names = 0
            while (_fmt) {
                if ((match = re.text.exec(_fmt)) !== null) {
                    parse_tree[parse_tree.length] = match[0]
                }
                else if ((match = re.modulo.exec(_fmt)) !== null) {
                    parse_tree[parse_tree.length] = "%"
                }
                else if ((match = re.placeholder.exec(_fmt)) !== null) {
                    if (match[2]) {
                        arg_names |= 1
                        var field_list = [], replacement_field = match[2], field_match = []
                        if ((field_match = re.key.exec(replacement_field)) !== null) {
                            field_list[field_list.length] = field_match[1]
                            while ((replacement_field = replacement_field.substring(field_match[0].length)) !== "") {
                                if ((field_match = re.key_access.exec(replacement_field)) !== null) {
                                    field_list[field_list.length] = field_match[1]
                                }
                                else if ((field_match = re.index_access.exec(replacement_field)) !== null) {
                                    field_list[field_list.length] = field_match[1]
                                }
                                else {
                                    throw new SyntaxError("[sprintf] failed to parse named argument key")
                                }
                            }
                        }
                        else {
                            throw new SyntaxError("[sprintf] failed to parse named argument key")
                        }
                        match[2] = field_list
                    }
                    else {
                        arg_names |= 2
                    }
                    if (arg_names === 3) {
                        throw new Error("[sprintf] mixing positional and named placeholders is not (yet) supported")
                    }
                    parse_tree[parse_tree.length] = match
                }
                else {
                    throw new SyntaxError("[sprintf] unexpected placeholder")
                }
                _fmt = _fmt.substring(match[0].length)
            }
            return parse_tree
        }

        var vsprintf = function (fmt, argv, _argv) {
            _argv = (argv || []).slice(0)
            _argv.splice(0, 0, fmt)
            return sprintf.apply(null, _argv)
        }

        /**
         * helpers
         */
        function get_type(variable) {
            return Object.prototype.toString.call(variable).slice(8, -1).toLowerCase()
        }

        function str_repeat(input, multiplier) {
            return Array(multiplier + 1).join(input)
        }

        /**
         * export to either browser or node.js
         */
        if (typeof exports !== "undefined") {
            exports.sprintf = sprintf
            exports.vsprintf = vsprintf
        }
        else {
            window.sprintf = sprintf
            window.vsprintf = vsprintf

            if (typeof define === "function" && define.amd) {
                define(function () {
                    return {
                        sprintf: sprintf,
                        vsprintf: vsprintf
                    }
                })
            }
        }

        return {
            sprintf: sprintf
        }
    })();


    // LSQR module including sample modle and tests
    (function(){
        // LSQR wrapper
        function lsqr(){
            var DBL_EPSILON = 2.2204460492503131e-16;

            // Interface of IO functions
            var iface = {
                print: function () {
                    var output=arguments[0];
                    var arg2=[];
                    for (var i=1; i<arguments.length; i++){
                        arg2.push(arguments[i]);
                    }
                    var str=sprintf.apply(null,arg2);
                    if (output instanceof Array){
                        output.push(str);
                    }else
                        console.log(str);
                }
            }


            // Private library functions
            {

                var max=function(a,b){
                    return a>b?a:b;
                }

                var sqr=function(val) {
                    // Note variable "casting" using +
                    val = +val;
                    return +(val * val);
                }

                var lsqr_error=function(msg, code) {
                    // We just throw an exception. Somebody will catch it, hopefully ;)
                    throw msg;
                }

                var alloc_lvec=function(count) {
                    var lng_vec = new Int32Array(count);
                    return lng_vec;
                }

                var free_lvec=function(vec) {
                    // Makes no sense in javascript, but we keep just in case we decide to use our own heap management in the future for
                    // asm.js
                };

                var alloc_dvec=function(count) {
                    var dbl_vec = new Float64Array(count);
                    return dbl_vec;
                }

                var free_dvec=function(vec) {
                    // Makes no sense in javascript
                }



                var dvec_norm2=function(vec) {
                    var indx;
                    var l;
                    var norm=0.0;

                    norm = 0.0;

                    for (indx = 0, l=vec.length; indx < l; indx++)
                        norm += sqr(vec[indx]);

                    return Math.sqrt(norm);
                }

                var dvec_scale=function(amount, vec) {
                    var indx;
                    var l;

                    for (indx = 0,l=vec.length; indx < l; indx++)
                        vec[indx] *= amount;

                    return;
                }

                var dvec_copy=function(src, dst) {
                    var indx;
                    var l=src.length;
                    for (indx = 0; indx < l; indx++)
                        dst[indx] = src[indx];
                }
            }


            function Model(params){
                var nrow=params.num_rows;
                var ncol=params.num_cols;

                var numElts;
                var rowIndex;
                var colStarts;
                var values;
                var rowUpper;
                var rowLower;
                var colUpper;
                var colLower;
                var rhs;
                var prod_data={
                    d_vec:null,
                    hy_vec:null,
                    hz_vec:null,
                    work_vec:null
                };


                var lstp_mult=function( h,x,y ){
                    /*
                     *     ------------------------------------------------------------------
                     *     HPROD  applies a Householder transformation stored in H to get
                     *     Y = ( I - 2*HZ*HZ(transpose) ) * X.
                     *     ------------------------------------------------------------------
                     */
                    var    vec_indx,vec_length;

                    var dwork;

                    var vec_length = h.length;
                    dwork = 0.0;

                    for( vec_indx = 0; vec_indx < vec_length; vec_indx++ )
                        dwork += h[vec_indx] * x[vec_indx];

                    dwork += dwork;

                    for( vec_indx = 0; vec_indx < vec_length; vec_indx++ )
                        y[vec_indx] = x[vec_indx] - dwork *
                        h[vec_indx];
                }



                var lstp=function( params){ // ojo.value

                    var duplicate_param=params.duplicate_param;
                    var power_param=params.power_param;
                    var damp_param=params.damp_param;
                    var act_sol_vec=params.act_sol_vec;
                    var act_rhs_vec=params.act_rhs_vec;
                    var test_prod=params.test_prod;
                    var act_mat_cond_num=params.act_mat_cond_num;
                    var act_resid_norm=params.act_resid_norm;

                    /*
                     *     ------------------------------------------------------------------
                     *     LSTP  generates a sparse least-squares test problem of the form
                     *
                     *                (   A    )*X = ( B )
                     *                ( DAMP*I )     ( 0 )
                     *
                     *     having a specified solution X.  The matrix A is constructed
                     *     in the form  A = HY*D*HZ,  where D is an 'num_rows' by 'num_cols'
                     *     diagonal matrix, and HY and HZ are Householder transformations.
                     *
                     *     The first 4 parameters are input to LSTP.  The remainder are
                     *     output.  LSTP is intended for use with 'num_rows' >= 'num_cols'.
                     *     ------------------------------------------------------------------
                     */

                    var num_rows,
                        num_cols,
                        row_indx,
                        col_indx,
                        lwork;

                    var   mnorm,
                        nnorm,
                        dwork;

                    num_rows = act_rhs_vec.length;
                    num_cols = act_sol_vec.length;
                    /*
                     *     Make two vectors of norm 1.0 for the Householder transformations.
                     */
                    for( row_indx = 0; row_indx < num_rows; row_indx++ )
                        test_prod.hy_vec[row_indx] =
                            Math.sin( +(row_indx + 1) * 4.0 * Math.PI / ( +(num_rows) ) );

                    for( col_indx = 0; col_indx < num_cols; col_indx++ )
                        test_prod.hz_vec[col_indx] =
                            Math.cos( +(col_indx + 1) * 4.0 * Math.PI / ( +(num_cols) ) );

                    mnorm = dvec_norm2( test_prod.hy_vec );
                    nnorm = dvec_norm2( test_prod.hz_vec );
                    dvec_scale( (-1.0 / mnorm), test_prod.hy_vec );
                    dvec_scale( (-1.0 / nnorm), test_prod.hz_vec );
                    /*
                     *     Set the diagonal matrix D.  These are the singular values of A.
                     */
                    for( col_indx = 0; col_indx < num_cols; col_indx++ )
                    {
                        lwork = ( col_indx + duplicate_param ) / duplicate_param;
                        dwork = +lwork * (+duplicate_param);
                        dwork /= +num_cols;
                        test_prod.d_vec[col_indx] = Math.pow( dwork, ( +power_param
                        ) );
                    }

                    act_mat_cond_num.value =
                        Math.sqrt((sqr(test_prod.d_vec[num_cols - 1]) + sqr(damp_param)) /
                        (sqr(test_prod.d_vec[0])            + sqr(damp_param)));
                    /*
                     *     Compute the residual vector, storing it in  B.
                     *     It takes the form  HY*( S )
                     *                           ( T )
                     *     where S is obtained from  D*S = DAMP**2 * HZ * X and T can be anything.
                     */
                    lstp_mult( test_prod.hz_vec, act_sol_vec, act_rhs_vec );

                    for( col_indx = 0; col_indx < num_cols; col_indx++ )
                        act_rhs_vec[col_indx] *= sqr( damp_param ) /
                        test_prod.d_vec[col_indx];

                    dwork = 1.0;
                    for( row_indx = num_cols; row_indx < num_rows; row_indx++ )
                    {
                        lwork = row_indx - (num_cols - 1);
                        act_rhs_vec[row_indx] = ( dwork * (+lwork) ) /
                        +(num_rows) ;
                        dwork = -dwork;
                    }

                    lstp_mult( test_prod.hy_vec, act_rhs_vec, act_rhs_vec );
                    /*
                     *     Now compute the true B = RESIDUAL + A*X.
                     */
                    mnorm = dvec_norm2( act_rhs_vec );
                    nnorm = dvec_norm2( act_sol_vec );
                    act_resid_norm.value = Math.sqrt( sqr( mnorm ) + sqr( damp_param ) * sqr( nnorm ) );

                    test_mult( 0, act_sol_vec, act_rhs_vec, test_prod );
                }


                var test_mult=function(mode,x,y,prod ){

                    /*
                     *     ------------------------------------------------------------------
                     *     This is the matrix-vector product routine required by LSQR
                     *     for a test matrix of the form  A = HY*D*HZ.  The quantities
                     *     defining D, HY, HZ and the work array W are in the structure data.
                     *     ------------------------------------------------------------------
                     */
                    var vec_indx;
                    var num_rows;
                    var num_cols;

                    var data=prod

                    num_cols = x.length;
                    num_rows = y.length;
                    /*
                     *     Compute  Y = Y + A*X
                     */
                    if( mode == 0 )
                    {
                        lstp_mult( data.hz_vec, x, data.work_vec );

                        for( vec_indx = 0; vec_indx < num_cols; vec_indx++ )
                            data.work_vec[vec_indx] *= data.d_vec[vec_indx];

                        for( vec_indx = num_cols; vec_indx < num_rows; vec_indx++ )
                            data.work_vec[vec_indx] = 0.0;

                        lstp_mult( data.hy_vec, data.work_vec, data.work_vec );

                        for( vec_indx = 0; vec_indx < num_rows; vec_indx++ )
                            y[vec_indx] += data.work_vec[vec_indx];
                    }
                    /*
                     *     Compute  X = X + A^T*Y
                     */
                    if( mode == 1 )
                    {
                        lstp_mult( data.hy_vec, y, data.work_vec );

                        for( vec_indx = 0; vec_indx < num_cols; vec_indx++ )
                            data.work_vec[vec_indx] *= data.d_vec[vec_indx];

                        lstp_mult( data.hz_vec, data.work_vec, data.work_vec );

                        for( vec_indx = 0; vec_indx < num_cols; vec_indx++ )
                            x[vec_indx] += data.work_vec[vec_indx];
                    }
                }

                function matVecMult( mode,x,y){
                    //  prod_data *prod
                    test_mult (mode, x, y, prod_data);
                    return;
                }
                return {
                    matVecMult:matVecMult,
                    rowSize:nrow,
                    colSize:ncol,
                    prod:prod_data,
                    lstp:lstp
                }
            }

            // Initialization. Expects a model with the appropriate interface
            function Lsqr(model) {
                var myModel = model;

                var input = {
                    num_rows:0,
                    num_cols:0,
                    damp_val:0,
                    rel_mat_err:0,
                    rel_rhs_err:0,
                    cond_lim:0,
                    max_iter:0,
                    lsqr_fp_out:null,
                    rhs_vec:null,
                    sol_vec:null
                };
                var output = {
                    term_flag:0,
                    num_iters:0,
                    frob_mat_norm:0,
                    mat_cond_num:0,
                    resid_norm:0,
                    mat_resid_norm:0,
                    sol_norm:0,
                    sol_vec:null,
                    std_err_vec:null
                };
                var work = {
                    bidiag_wrk_vec:undefined,
                    srch_dir_vec:undefined
                };

                input.num_rows = model.rowSize;
                input.num_cols = model.colSize;
                input.damp_val = 0.0;
                input.rel_mat_err = 0.0;
                input.rel_rhs_err = 0.0;
                input.cond_lim = 1.e15;
                input.max_iter = 99999999;
                input.lsqr_fp_out = 0;
                input.rhs_vec = 0;
                input.sol_vec = 0;




                function allocLsqrMem() {

                    var max_num_rows = input.num_rows;
                    var max_num_cols = input.num_cols;

                    var temp_vec = alloc_dvec(max_num_rows);
                    input.rhs_vec = temp_vec;
                    //  input->rhs_vec = (dvec *) alloc_dvec( max_num_rows );
                    if (!input.rhs_vec) lsqr_error("lsqr: right hand side vector \'b\' allocation failure in function allocLsqrMem()", -1);

                    input.sol_vec = alloc_dvec(max_num_cols);
                    if (!input.sol_vec)lsqr_error("lsqr: solution vector \'x\' allocation  failure in function allocLsqrMem()", -1);

                    output.std_err_vec = alloc_dvec(max_num_cols);
                    if (!output.std_err_vec) lsqr_error("lsqr: standard error vector \'e\' allocation failure in function allocLsqrMem()", -1);

                    output.sol_vec = input.sol_vec;

                    work.bidiag_wrk_vec = alloc_dvec(max_num_cols);
                    if (!work.bidiag_wrk_vec) lsqr_error("lsqr: bidiagonalization work vector \'v\' allocation failure in function allocLsqrMem()", -1);

                    work.srch_dir_vec = alloc_dvec(max_num_cols);
                    if (!work.srch_dir_vec)
                        lsqr_error("lsqr: search direction vector \'w\' allocation failure in function allocLsqrMem()", -1);
                }

                function freeLsqrMem() {
                    free_dvec(input.rhs_vec);
                    free_dvec(input.sol_vec);
                    free_dvec(output.std_err_vec);
                    free_dvec(work.bidiag_wrk_vec);
                    free_dvec(work.srch_dir_vec);
                    return;

                }

                function do_lsqr(model) {

//                double  dvec_norm2( dvec * );

                    var indx,
                        num_iter,
                        term_iter,
                        term_iter_max;

                    var alpha,
                        beta,
                        rhobar,
                        phibar,
                        bnorm,
                        bbnorm,
                        cs1,
                        sn1,
                        psi,
                        rho,
                        cs,
                        sn,
                        theta,
                        phi,
                        tau,
                        ddnorm,
                        delta,
                        gammabar,
                        zetabar,
                        gamma_,
                        cs2,
                        sn2,
                        zeta,
                        xxnorm,
                        res,
                        resid_tol,
                        cond_tol,
                        resid_tol_mach,
                        temp,
                        stop_crit_1,
                        stop_crit_2,
                        stop_crit_3;

                    var term_msg = [
                        "The exact solution is x = x0",
                        "The residual Ax - b is small enough, given ATOL and BTOL",
                        "The least squares error is small enough, given ATOL",
                        "The estimated condition number has exceeded CONLIM",
                        "The residual Ax - b is small enough, given machine precision",
                        "The least squares error is small enough, given machine precision",
                        "The estimated condition number has exceeded machine precision",
                        "The iteration limit has been reached"

                    ]

                    var outFile=input.lsqr_fp_out

                    if (outFile) {
                        iface.print(outFile,"  Least Squares Solution of A*x = b\n" +
                            "The matrix A has %7i rows and %7i columns\n" +
                            "The damping parameter is\tDAMP = %10.2e\n" +
                            "ATOL = %10.2e\t\tCONDLIM = %10.2e\n" +
                            "BTOL = %10.2e\t\tITERLIM = %10i\n\n",
                            input.num_rows, input.num_cols, input.damp_val, input.rel_mat_err,
                            input.cond_lim, input.rel_rhs_err, input.max_iter);
                    }

                    output.term_flag = 0;
                    term_iter = 0;

                    output.num_iters = 0;
                    output.frob_mat_norm = 0.0;
                    output.mat_cond_num = 0.0;
                    output.sol_norm = 0.0;

                    for (indx = 0; indx < input.num_cols; indx++) {
                        work.bidiag_wrk_vec[indx] = 0.0;
                        work.srch_dir_vec[indx] = 0.0;
                        output.std_err_vec[indx] = 0.0;
                    }

                    bbnorm = 0.0;
                    ddnorm = 0.0;
                    xxnorm = 0.0;

                    cs2 = -1.0;
                    sn2 = 0.0;
                    zeta = 0.0;
                    res = 0.0;

                    if (input.cond_lim > 0.0)
                        cond_tol = 1.0 / input.cond_lim;
                    else
                        cond_tol = DBL_EPSILON;

                    alpha = 0.0;
                    beta = 0.0;
                    /*
                     *  Set up the initial vectors u and v for bidiagonalization.  These satisfy
                     *  the relations
                     *             BETA*u = b - A*x0
                     *             ALPHA*v = A^T*u
                     */
                    /* Compute b - A*x0 and store in vector u which initially held vector b */
                    dvec_scale((-1.0), input.rhs_vec);
                    model.matVecMult(0, input.sol_vec, input.rhs_vec);
                    dvec_scale((-1.0), input.rhs_vec);

                    /* compute Euclidean length of u and store as BETA */
                    beta = dvec_norm2(input.rhs_vec);

                    if (beta > 0.0) {
                        /* scale vector u by the inverse of BETA */
                        dvec_scale((1.0 / beta), input.rhs_vec);

                        /* Compute matrix-vector product A^T*u and store it in vector v */
                        model.matVecMult(1, work.bidiag_wrk_vec, input.rhs_vec);

                        /* compute Euclidean length of v and store as ALPHA */
                        alpha = dvec_norm2(work.bidiag_wrk_vec);
                    }

                    if (alpha > 0.0) {
                        /* scale vector v by the inverse of ALPHA */
                        dvec_scale((1.0 / alpha), work.bidiag_wrk_vec);

                        /* copy vector v to vector w */
                        dvec_copy(work.bidiag_wrk_vec, work.srch_dir_vec);
                    }

                    output.mat_resid_norm = alpha * beta;
                    output.resid_norm = beta;
                    bnorm = beta;
                    /*
                     *  If the norm || A^T r || is zero, then the initial guess is the exact
                     *  solution.  Exit and report this.
                     */
                    if ((output.mat_resid_norm == 0.0) && (input.lsqr_fp_out)) {
                        iface.print(outFile,"\tISTOP = %3i\t\t\tITER = %9i\n" +
                            "|| A ||_F = %13.5e\tcond( A ) = %13.5e\n" +
                            "|| r ||_2 = %13.5e\t|| A^T r ||_2 = %13.5e\n" +
                            "|| b ||_2 = %13.5e\t|| x - x0 ||_2 = %13.5e\n\n",
                            output.term_flag, output.num_iters, output.frob_mat_norm,
                            output.mat_cond_num, output.resid_norm, output.mat_resid_norm,
                            bnorm, output.sol_norm);
                        iface.print(outFile,term_msg[output.term_flag]);
                        return;
                    }

                    rhobar = alpha;
                    phibar = beta;
                    /*
                     *  If statistics are printed at each iteration, print a header and the initial
                     *  values for each quantity.
                     */
                    if (input.lsqr_fp_out) {
                        iface.print(outFile,
                            "  ITER     || r ||    Compatible  " +
                            "||A^T r|| / ||A|| ||r||  || A ||    cond( A )\n\n");

                        stop_crit_1 = 1.0;
                        stop_crit_2 = alpha / beta;

                        iface.print(outFile,
                            "%6i %13.5e %10.2e \t%10.2e \t%10.2e  %10.2e\n",
                            output.num_iters, output.resid_norm, stop_crit_1, stop_crit_2,
                            output.frob_mat_norm, output.mat_cond_num);
                    }

                    /*
                     *  The main iteration loop is continued as long as no stopping criteria
                     *  are satisfied and the number of total iterations is less than some upper
                     *  bound.
                     */
                    while (output.term_flag == 0) {
                        output.num_iters++;
                        /*
                         *     Perform the next step of the bidiagonalization to obtain
                         *     the next vectors u and v, and the scalars ALPHA and BETA.
                         *     These satisfy the relations
                         *                BETA*u  =  A*v  -  ALPHA*u,
                         *                ALFA*v  =  A^T*u  -  BETA*v.
                         */
                        /* scale vector u by the negative of ALPHA */
                        dvec_scale((-alpha), input.rhs_vec);

                        /* compute A*v - ALPHA*u and store in vector u */
                        model.matVecMult(0, work.bidiag_wrk_vec, input.rhs_vec);

                        /* compute Euclidean length of u and store as BETA */
                        beta = dvec_norm2(input.rhs_vec);

                        /* accumulate this quantity to estimate Frobenius norm of matrix A */
                        bbnorm += sqr(alpha) + sqr(beta) + sqr(input.damp_val);

                        if (beta > 0.0) {
                            /* scale vector u by the inverse of BETA */
                            dvec_scale((1.0 / beta), input.rhs_vec);

                            /* scale vector v by the negative of BETA */
                            dvec_scale((-beta), work.bidiag_wrk_vec);

                            /* compute A^T*u - BETA*v and store in vector v */
                            model.matVecMult(1, work.bidiag_wrk_vec, input.rhs_vec);

                            /* compute Euclidean length of v and store as ALPHA */
                            alpha = dvec_norm2(work.bidiag_wrk_vec);

                            if (alpha > 0.0)
                            /* scale vector v by the inverse of ALPHA */
                                dvec_scale((1.0 / alpha), work.bidiag_wrk_vec);
                        }
                        /*
                         *     Use a plane rotation to eliminate the damping parameter.
                         *     This alters the diagonal (RHOBAR) of the lower-bidiagonal matrix.
                         */
                        cs1 = rhobar / Math.sqrt(sqr(+rhobar) + sqr(+input.damp_val));
                        sn1 = input.damp_val / Math.sqrt(sqr(+rhobar) + sqr(+input.damp_val));

                        psi = sn1 * phibar;
                        phibar = cs1 * phibar;
                        /*
                         *     Use a plane rotation to eliminate the subdiagonal element (BETA)
                         *     of the lower-bidiagonal matrix, giving an upper-bidiagonal matrix.
                         */
                        rho = Math.sqrt(sqr(rhobar) + sqr(input.damp_val) + sqr(beta));
                        cs = Math.sqrt(sqr(rhobar) + sqr(input.damp_val)) / rho;
                        sn = beta / rho;

                        theta = sn * alpha;
                        rhobar = -cs * alpha;
                        phi = cs * phibar;
                        phibar = sn * phibar;
                        tau = sn * phi;
                        /*
                         *     Update the solution vector x, the search direction vector w, and the
                         *     standard error estimates vector se.
                         */
                        for (indx = 0; indx < input.num_cols; indx++) {
                            /* update the solution vector x */
                            output.sol_vec[indx] += (phi / rho) *
                            work.srch_dir_vec[indx];

                            /* update the standard error estimates vector se */
                            output.std_err_vec[indx] += sqr((1.0 / rho) *
                            work.srch_dir_vec[indx]);

                            /* accumulate this quantity to estimate condition number of A
                             */
                            ddnorm += sqr((1.0 / rho) * work.srch_dir_vec[indx]);

                            /* update the search direction vector w */
                            work.srch_dir_vec[indx] =
                                work.bidiag_wrk_vec[indx] -
                                (theta / rho) * work.srch_dir_vec[indx];
                        }
                        /*
                         *     Use a plane rotation on the right to eliminate the super-diagonal element
                         *     (THETA) of the upper-bidiagonal matrix.  Then use the result to estimate
                         *     the solution norm || x ||.
                         */
                        delta = sn2 * rho;
                        gammabar = -cs2 * rho;
                        zetabar = (phi - delta * zeta) / gammabar;

                        /* compute an estimate of the solution norm || x || */
                        output.sol_norm = Math.sqrt(xxnorm + sqr(zetabar));

                        gamma_ = Math.sqrt(sqr(gammabar) + sqr(theta));
                        cs2 = gammabar / gamma_;
                        sn2 = theta / gamma_;
                        zeta = (phi - delta * zeta) / gamma_;

                        /* accumulate this quantity to estimate solution norm || x || */
                        xxnorm += sqr(zeta);
                        /*
                         *     Estimate the Frobenius norm and condition of the matrix A, and the
                         *     Euclidean norms of the vectors r and A^T*r.
                         */
                        output.frob_mat_norm = Math.sqrt(bbnorm);
                        output.mat_cond_num = output.frob_mat_norm * Math.sqrt(ddnorm);

                        res += sqr(psi);
                        output.resid_norm = Math.sqrt(sqr(phibar) + res);

                        output.mat_resid_norm = alpha * Math.abs(tau);
                        /*
                         *     Use these norms to estimate the values of the three stopping criteria.
                         */
                        stop_crit_1 = output.resid_norm / bnorm;

                        stop_crit_2 = 0.0;
                        if (output.resid_norm > 0.0)
                            stop_crit_2 = output.mat_resid_norm / ( output.frob_mat_norm *
                            output.resid_norm );

                        stop_crit_3 = 1.0 / output.mat_cond_num;

                        resid_tol = input.rel_rhs_err + input.rel_mat_err *
                        output.mat_resid_norm *
                        output.sol_norm / bnorm;

                        resid_tol_mach = DBL_EPSILON + DBL_EPSILON * output.mat_resid_norm *
                        output.sol_norm / bnorm;
                        /*
                         *     Check to see if any of the stopping criteria are satisfied.
                         *     First compare the computed criteria to the machine precision.
                         *     Second compare the computed criteria to the the user specified precision.
                         */
                        /* iteration limit reached */
                        if (output.num_iters >= input.max_iter)
                            output.term_flag = 7;

                        /* condition number greater than machine precision */
                        if (stop_crit_3 <= DBL_EPSILON)
                            output.term_flag = 6;
                        /* least squares error less than machine precision */
                        if (stop_crit_2 <= DBL_EPSILON)
                            output.term_flag = 5;
                        /* residual less than a function of machine precision */
                        if (stop_crit_1 <= resid_tol_mach)
                            output.term_flag = 4;

                        /* condition number greater than CONLIM */
                        if (stop_crit_3 <= cond_tol)
                            output.term_flag = 3;
                        /* least squares error less than ATOL */
                        if (stop_crit_2 <= input.rel_mat_err)
                            output.term_flag = 2;
                        /* residual less than a function of ATOL and BTOL */
                        if (stop_crit_1 <= resid_tol)
                            output.term_flag = 1;
                        /*
                         *  If statistics are printed at each iteration, print a header and the initial
                         *  values for each quantity.
                         */
                        if (input.lsqr_fp_out) {
                            iface.print(outFile,
                                "%6i %13.5e %10.2e \t%10.2e \t%10.2e %10.2e\n",
                                output.num_iters, output.resid_norm, stop_crit_1,
                                stop_crit_2,
                                output.frob_mat_norm, output.mat_cond_num);
                        }
                        /*
                         *     The convergence criteria are required to be met on NCONV consecutive
                         *     iterations, where NCONV is set below.  Suggested values are 1, 2, or 3.
                         */
                        if (output.term_flag == 0)
                            term_iter = -1;

                        term_iter_max = 1;
                        term_iter++;

                        if ((term_iter < term_iter_max) &&
                            (output.num_iters < input.max_iter))
                            output.term_flag = 0;
                    }
                    /* end while loop */
                    /*
                     *  Finish computing the standard error estimates vector se.
                     */
                    temp = 1.0;

                    if (input.num_rows > input.num_cols)
                        temp = +(input.num_rows - input.num_cols);

                    if (sqr(input.damp_val) > 0.0)
                        temp = +(input.num_rows);

                    temp = output.resid_norm / Math.sqrt(temp);

                    for (indx = 0; indx < input.num_cols; indx++)
                        /* update the standard error estimates vector se */
                        output.std_err_vec[indx] = temp *
                        Math.sqrt(output.std_err_vec[indx]);
                    /*
                     *  If statistics are printed at each iteration, print the statistics for the
                     *  stopping condition.
                     */
                    if (input.lsqr_fp_out) {
                        iface.print(outFile,"\n\tISTOP = %3i\t\t\tITER = %9i\n" +
                            "|| A ||_F = %13.5e\tcond( A ) = %13.5e\n" +
                            "|| r ||_2 = %13.5e\t|| A^T r ||_2 = %13.5e\n" +
                            "|| b ||_2 = %13.5e\t|| x - x0 ||_2 = %13.5e\n\n",
                            output.term_flag, output.num_iters, output.frob_mat_norm,
                            output.mat_cond_num, output.resid_norm, output.mat_resid_norm,
                            bnorm, output.sol_norm);
                        iface.print(outFile,term_msg[output.term_flag]);
                    }
                }


                return{
                    do_lsqr:do_lsqr,
                    allocLsqrMem:allocLsqrMem,
                    freeLsqrMem:freeLsqrMem,
                    input:input,
                    output:output,
                    work:work
                }

            }

            function test_lsqr(params){
                var num_rows=params.num_rows;
                var num_cols=params.num_cols;
                var duplicate_param=params.duplicate_param;
                var power_param=params.power_param;
                var damp_param=params.damp_param;
                var outFile=params.output;

                var col_indx;

                var unorm,
                    enorm,
                    etol;
                var act_mat_cond_num={value:0};
                var act_resid_norm={value:0};

                var act_rhs_vec;
                var act_sol_vec;

                // Instantiate the model
                var model=Model({num_rows:num_rows,num_cols:num_cols});

                // and then Lsqr
                var lsqr = new Lsqr(model);

                // Allocate memory for lsqr
                lsqr.allocLsqrMem();

                // Specify output unit
                lsqr.input.lsqr_fp_out = outFile;

                /*
                 *     Allocate the space for the data structure of type 'prod_data'.
                 */

                model.prod.d_vec = alloc_dvec( num_cols );
                if (!model.prod.d_vec) lsqr_error("test_prog: vector \'d\' allocation failure in function lsqr_test()", -1);

                model.prod.hy_vec = alloc_dvec( num_rows );
                if (!model.prod.hy_vec) lsqr_error("test_prog: vector \'hy\' allocation failure in function lsqr_test()", -1);

                model.prod.hz_vec = alloc_dvec( num_cols );
                if (!model.prod.hz_vec) lsqr_error("test_prog: vector \'hz\' allocation failure in function lsqr_test()", -1);

                model.prod.work_vec = alloc_dvec( max( num_rows, num_cols ) );
                if (!model.prod.work_vec) lsqr_error("test_prog: vector \'work\' allocation failure in function lsqr_test()", -1);
                /*
                 *     Allocate the other needed vectors.
                 */
                act_rhs_vec = alloc_dvec( num_rows );
                if (!act_rhs_vec) lsqr_error("test_prog: vector \'b\' allocation failure in function lsqr_test()", -1);

                act_sol_vec = alloc_dvec( num_cols );
                if (!act_sol_vec) lsqr_error("test_prog: vector \'x_ans\' allocation failure in function lsqr_test()", -1);
                /*
                 *     Set the true solution for the test problem.
                 */
                for( col_indx = 0; col_indx < num_cols; col_indx++ )
                    act_sol_vec[col_indx] = ( num_cols - (col_indx + 1) );
                /*
                 *     Call the routine LSTP which generates the least squares test problem.
                 */
                model.lstp( {
                    duplicate_param:duplicate_param,
                    power_param:power_param,
                    damp_param:damp_param,
                    act_sol_vec:act_sol_vec,
                    act_rhs_vec:act_rhs_vec,
                    test_prod:model.prod,
                    act_mat_cond_num:act_mat_cond_num,
                    act_resid_norm:act_resid_norm });
                /*
                 *     Copy the right-hand side vector generated for the test problem by LSTP
                 *     into the right-hand side vector for LSQR.
                 */
                dvec_copy( act_rhs_vec, lsqr.input.rhs_vec );
                /*
                 *  Set the initial guess for LSQR.
                 */
                for( col_indx = 0; col_indx < num_cols; col_indx++ )
                    lsqr.input.sol_vec[col_indx] = 0.0;
                /*
                 *     Print information about the test problem.
                 */
                iface.print(outFile,"--------------------------------------------------------------------\n" );
                iface.print(outFile,"Least-Squares Test Problem      P( %5i %5i %5i %5i %12.2e )\n\n",
                    num_rows, num_cols, duplicate_param, power_param, damp_param );
                iface.print(outFile,"Condition No. = %12.4e     Residual Function = %17.9e\n",
                    act_mat_cond_num.value, act_resid_norm.value );
                iface.print("--------------------------------------------------------------------\n\n" );
                /*
                 *     Set the input parameters for LSQR.
                 */
                lsqr.input.num_rows = num_rows;
                lsqr.input.num_cols = num_cols;
                lsqr.input.damp_val = damp_param;
                lsqr.input.rel_mat_err = 1.0e-10;
                lsqr.input.rel_rhs_err = 1.0e-10;
                lsqr.input.cond_lim = 10.0 * act_mat_cond_num.value;
                lsqr.input.max_iter = num_rows + num_cols + 50;
                /*
                 *     Solve the test problem generated by LTSP by calling the routine LSQR.
                 */
                lsqr.do_lsqr( model);

                /*
                 *     Examine the results.
                 *     Print the residual norms RNORM and ARNORM given by LSQR, and then compute
                 *     their true values in terms of the solution X obtained by  LSQR.
                 *     At least one of these norms should be small.
                 */
                iface.print(outFile,"\t\t\tResidual Norm       Residual Norm       Solution Norm\n" );
                iface.print(outFile,"\t\t\t||A x - b||_2   ||A^T A x - A^T b||_2   ||x - x0||_2\n\n" );
                iface.print(outFile,"Estimated by LSQR  %17.5e   %17.5e   %17.5e\n",
                    lsqr.output.resid_norm, lsqr.output.mat_resid_norm, lsqr.output.sol_norm );
                /*
                 *     Compute  U = A*x - b.
                 *     This is the negative of the usual residual vector.  It will be close to
                 *     zero only if b is a compatible rhs and x is close to a solution.
                 */
                dvec_copy( act_rhs_vec, lsqr.input.rhs_vec );
                dvec_scale( (-1.0), lsqr.input.rhs_vec );
                model.matVecMult( 0, lsqr.output.sol_vec, lsqr.input.rhs_vec, model.prod );
                /*
                 *     Compute  v = A^T*u  +  DAMP**2 * x.
                 *     This will be close to zero in all cases if x is close to a solution.
                 */
                dvec_copy( lsqr.output.sol_vec, lsqr.work.bidiag_wrk_vec );
                dvec_scale( ( sqr(damp_param) ), lsqr.work.bidiag_wrk_vec );
                model.matVecMult( 1, lsqr.work.bidiag_wrk_vec, lsqr.input.rhs_vec, model.prod );
                /*
                 *     Compute the norms associated with  x, u, v.
                 */
                lsqr.output.sol_norm = dvec_norm2( lsqr.output.sol_vec );
                unorm = dvec_norm2( lsqr.input.rhs_vec );
                lsqr.output.resid_norm = Math.sqrt( sqr( unorm ) + sqr( damp_param ) *
                sqr( lsqr.output.sol_norm ) );
                lsqr.output.mat_resid_norm = dvec_norm2( lsqr.work.bidiag_wrk_vec );
                iface.print(outFile,"Computed from X    %17.5e   %17.5e   %17.5e\n\n",
                    lsqr.output.resid_norm, lsqr.output.mat_resid_norm, lsqr.output.sol_norm );
                /*
                 *     Print the solution and standard error estimates from LSQR.
                 */
                iface.print(outFile,"Solution X\n" );
                for( col_indx = 0; col_indx < num_cols; col_indx++ )
                {
                    iface.print(outFile, "%6i %14.6g", col_indx,
                        lsqr.output.sol_vec[col_indx] );
                    if( ( (col_indx + 1) % 4 ) == 0 )
                        iface.print(outFile,"\n" );
                }

                iface.print(outFile,"\n\n" );

                iface.print(outFile,"Standard Errors SE\n" );
                for( col_indx = 0; col_indx < num_cols; col_indx++ )
                {
                    iface.print(outFile,"%6i %14.6g", col_indx,
                        lsqr.output.std_err_vec[col_indx] );
                    if( ( (col_indx + 1) % 4 ) == 0 )
                        iface.print(outFile,"\n" );
                }
                iface.print(outFile,"\n\n" );
                /*
                 *     Print information about the accuracy of the LSQR solution.
                 */
                for( col_indx = 0; col_indx < num_cols; col_indx++ )
                    lsqr.work.srch_dir_vec[col_indx] =
                        lsqr.output.sol_vec[col_indx]
                        - act_sol_vec[col_indx];

                enorm = dvec_norm2( lsqr.work.srch_dir_vec ) /
                ( 1.0 + dvec_norm2( act_sol_vec ) );
                etol = 1.0e-5;

                if( enorm <= etol )
                    iface.print(outFile,"LSQR appears to be successful.    Relative error in X = %10.2e\n\n",
                        enorm );
                if( enorm > etol )
                    iface.print(outFile,"LSQR appears to have failed.      Relative error in X = %10.2e\n\n",
                        enorm );
                /*
                 *     Free the memory allocated for LSQR.
                 */
                lsqr.freeLsqrMem();

                free_dvec( model.prod.d_vec );
                free_dvec( model.prod.hy_vec );
                free_dvec( model.prod.hz_vec );
                free_dvec( model.prod.work_vec );
                //  free( (prod_data *) (prod) );

                free_dvec( act_rhs_vec );
                free_dvec( act_sol_vec );
            }


            function fullTest(output){
                 var  damp1,
                 damp2,
                 damp3,
                 damp4;

                 damp1 = 0.1;
                 damp2 = 0.01;
                 damp3 = 0.001;
                 damp4 = 0.0001;

                test_lsqr({num_rows:1,num_cols:1,duplicate_param:1,power_param:1,damp_param:0,output:output});
                test_lsqr({num_rows:2,num_cols:1,duplicate_param:1,power_param:1,damp_param:0,output:output});
                test_lsqr({num_rows:40,num_cols:40,duplicate_param:4,power_param:4,damp_param:0,output:output});
                test_lsqr({num_rows:80,num_cols:80,duplicate_param:4,power_param:4,damp_param:damp2,output:output});
                test_lsqr({num_rows:10,num_cols:10,duplicate_param:1,power_param:8,damp_param:damp2,output:output});

                test_lsqr({num_rows:40,num_cols:40,duplicate_param:4,power_param:7,damp_param:0,output:output});
                test_lsqr({num_rows:80,num_cols:40,duplicate_param:4,power_param:6,damp_param:0,output:output});
                test_lsqr({num_rows:20,num_cols:10,duplicate_param:1,power_param:6,damp_param:0,output:output});
                test_lsqr({num_rows:20,num_cols:10,duplicate_param:1,power_param:8,damp_param:0,output:output});
            }

            return{
                Model:Model, // Returns a model
                Lsqr:Lsqr, // Returns the Lsqr interface
                test_lsqr:test_lsqr, // Returns the test functions
                fullTest:fullTest // Performs a set of tests and returns them in the output array. Please see lsqrTest.html for more info
            }

        }
        window.lsqr=lsqr();
    })();;


})();

