/**
 * Created by SANTI on 26/10/2015.
 *
 * Módulo que se encarga de resolver problemas no lineales basados en restricciones.
 *
 */


(function () {
    "use strict";
    console.log("constrainedSolver module");
    angular.module('constrainedSolver', [])
        .factory('constrainedSolver', ['sylvester', 'lsqr', function (sylvester, lsqr) {
            "use strict"
            console.log("constrainedSolver factory");
            function newInstance(iface) {

                /* EJEMPLO DE MATRIZ

                 [ 1  0  3  0
                 0  5  0  6
                 0  0  0  7]

                 elements:[1,3,5,6,7]
                 hashElements:[0,0,0,b0,0,2,1,b1,1,1,2,b2,1,3,3,b3,3,3,4,b4] // bn --> El siguiente hermano para la misma hash
                 hashHeads: [-1,-1,-1] // Inicialmente a -1, nos indica el índice en la tabla hashElements donde empieza el primer elemento con esta hash

                 */

                var _lsqr;
                var _sparseJacobian;

                function newJacobian(params) {
                    if (!params) {
                        params = {};
                    }
                    var hashBits = params.hashBits || 16;
                    var hashBits2 = (hashBits / 2) | 0;
                    if (hashBits2 * 2 != hashBits) {
                        throw "hashBits must be an even number"
                    }
                    if (hashBits > 16) {
                        throw "hashBits must be less or equal to 16"
                    }
                    var hashSize = 1 << hashBits;
                    var hashLower = 0;

                    for (var i = 0; i < hashBits2; i++) {
                        hashLower |= 1 << i;
                    }

                    var numRows = 0;
                    var numCols = 0;
                    var elements = [];
                    var hashElements = []; // [iRow,iCol,iElement,iBrother,iRow,iCol,iElement,iBrother...]
                    var hashHeads = new Int32Array(hashSize);
                    var fast_elements = null;
                    var consolidated = false;
                    var fast_hashElements;

                    for (var i = 0; i < hashHeads.length; i++) {
                        hashHeads[i] = -1;
                    }

                    function reset() {
                        numRows = 0;
                        numCols = 0;
                        consolidated = false;
                        for (var i = 0, ic = elements.length; i < ic; i++) {
                            elements[i] = 0;
                        }
                        for (var i = 0; i < hashHeads.length; i++) {
                            hashHeads[i] = -1;
                        }
                        elements = [];
                        hashElements = [];
                        fast_elements = null;
                        fast_hashElements = null;
                    }

                    function consolidate() {
                        fast_elements = new Float64Array(elements);
                        fast_hashElements = new Int32Array(hashElements);
                        consolidated = true;
                    }

                    function setElement(iRow, iCol, value) { // Establece un elemento de la matriz sparse
                        iRow = iRow | 0;
                        iCol = iCol | 0;
                        value = +value;
                        if (iRow + 1 > numRows) {
                            numRows = (iRow + 1) | 0;
                            consolidated = false;
                        }
                        if (iCol + 1 > numCols) {
                            numCols = (iCol + 1) | 0;
                            consolidated = false;
                        }
                        if (consolidated) {
                            var hash = (((iRow << hashBits2) | (iCol & hashLower)) % hashSize) | 0;
                            var iter = hashHeads[hash] | 0;
                            while (iter != -1) {
                                if (fast_hashElements[iter] == iRow && fast_hashElements[iter + 1] == iCol) {
                                    var elementIndex = fast_hashElements[iter + 2];
                                    fast_elements[elementIndex] = value;
                                    return;
                                }
                                iter = fast_hashElements[iter + 3];
                            }
                            var index = hashElements.length;
                            hashElements.push(iRow);
                            hashElements.push(iCol);
                            var elementIndex = elements.length;
                            hashElements.push(elementIndex);
                            elements.push(value);
                            hashElements.push(hashHeads[hash]); // mi hermano es la cabeza de la lista
                            hashHeads[hash] = index; // la cabeza de la lista soy yo
                            consolidated = false;
                        } else {
                            var hash = (((iRow << hashBits2) | (iCol & hashLower)) % hashSize) | 0;
                            var iter = hashHeads[hash];
                            while (iter != -1) {
                                if (hashElements[iter] == iRow && hashElements[iter + 1] == iCol) {
                                    var elementIndex = hashElements[iter + 2];
                                    elements[elementIndex] = value;
                                    return;
                                }
                                iter = hashElements[iter + 3];
                            }
                            var index = hashElements.length;
                            hashElements.push(iRow);
                            hashElements.push(iCol);
                            var elementIndex = elements.length;
                            hashElements.push(elementIndex);
                            elements.push(value);
                            hashElements.push(hashHeads[hash]); // mi hermano es la cabeza de la lista
                            hashHeads[hash] = index; // la cabeza de la lista soy yo
                            consolidated = false;
                        }

                    };

                    function getElement(iRow, iCol) {
                        var hash = (((iRow << hashBits2) | (iCol & hashLower)) % hashSize) | 0;
                        var iter = hashHeads[hash] | 0;
                        if (consolidated) {
                            while (iter != -1) {
                                if (fast_hashElements[iter | 0] == iRow && fast_hashElements[(iter + 1) | 0] == iCol) {
                                    var elementIndex = fast_hashElements[(iter + 2) | 0] | 0;
                                    return fast_elements[elementIndex | 0];
                                }
                                iter = fast_hashElements[(iter + 3) | 0] | 0;
                            }
                        } else {
                            while (iter != -1) {
                                if (hashElements[iter] == iRow && hashElements[iter + 1] == iCol) {
                                    var elementIndex = hashElements[iter + 2];
                                    return elements[elementIndex];
                                }
                                iter = hashElements[iter + 3];
                            }
                        }
                    }


                    function multPlus(vectorX, vectorY) {
                        if (!consolidated) {
                            consolidate();
                        }
                        for (var i = 0, ic = fast_hashElements.length | 0; i < ic; i = (i + 4) | 0) {
                            var row = fast_hashElements[i] | 0;
                            var col = fast_hashElements[(i + 1) | 0] | 0;
                            var iElement = fast_hashElements[(i + 2) | 0] | 0;
                            vectorY[row | 0] += (+fast_elements[iElement | 0]) * (+vectorX[col | 0]);
                        }
                    }

                    function multTPlus(vectorX, vectorY) {
                        if (!consolidated) {
                            consolidate();
                        }
                        for (var i = 0, ic = fast_hashElements.length | 0; i < ic; i += 4) {
                            var row = fast_hashElements[i] | 0;
                            var col = fast_hashElements[i + 1] | 0;
                            var iElement = fast_hashElements[i + 2] | 0;
                            vectorX[col | 0] += (+fast_elements[iElement | 0]) * (+vectorY[row | 0]);
                        }
                    }

                    function toSylvesterMatrix() {
                        if (!consolidated)
                            consolidate();
                        var sparseElements = this.elements;
                        var rowCount = numRows;
                        var colCount = numCols;
                        var elements = [];
                        for (var i = 0; i < rowCount; i++) {
                            elements[i] = [];
                            for (var j = 0; j < colCount; j++) {
                                elements[i][j] = 0;
                            }
                        }
                        for (var i = 0; i < fast_hashElements.length; i += 4) {
                            var iRow = fast_hashElements[i];
                            var iCol = fast_hashElements[i + 1];
                            var iElement = fast_hashElements[i + 2];
                            elements[iRow][iCol] = fast_elements[iElement];
                        }

                        var matrix = sylvester.Matrix.create(elements);
                        return matrix;
                    }


                    return {
                        getNumRows: function () {
                            return numRows
                        },
                        getNumCols: function () {
                            return numCols
                        },
                        reset: reset,
                        consolidate: consolidate,
                        setElement: setElement,
                        getElement: getElement, // Gets the element
                        multPlus: multPlus,
                        multTPlus: multTPlus,
                        toSylvesterMatrix: toSylvesterMatrix
                    }

                }

                // Le pasamos la lista de constraints, que seran los rows del problema.
                // Para cada constraint, necesitamos una lista de aquellas cols (variables) con las que
                // está asociada (potencialmente tiene un valor distinto de cero)
                function init(params) {
                    var constraints = params.constraints;
                    _sparseJacobian = newJacobian();
                    for (var i = 0, ic = constraints.length; i < ic; i++) {
                        var constraint = constraints[i];
                        var variables = constraint.variables;
                        for (var j = 0, jc = variables.length; j < jc; j++) {
                            var variableIndex = variables[j];
                            _sparseJacobian.setElement(i, variableIndex, 0);
                        }
                    }
                    _lsqr = lsqr.newInstance({
                        rowSize: _sparseJacobian.getNumRows(),
                        colSize: _sparseJacobian.getNumCols(),
                        matVecMult: function (mode, x, y) {
                            switch (mode) {
                                case 0:
                                    _sparseJacobian.multPlus(x, y);
                                    break;
                                case 1:
                                    _sparseJacobian.multTPlus(x, y);
                                    break;
                            }
                        }
                    });
                }

                function evaluate(params) {
                    var vectorX = params.vectorX;
                    var vectorY = params.vectorY;
                    var calculateDifferentials = params.calculateDifferentials;
                    var numVariables = _sparseJacobian.getNumCols();
                    if (vectorX.length != numVariables) {
                        throw "Invalid solution. Solution and variable size do not match"
                    }
                    iface.evaluate({
                        vectorX: vectorX,
                        vectorY: vectorY,
                        jacobian: _sparseJacobian,
                        calculateDifferentials: calculateDifferentials
                    });
                }

                function solve(params) {
                    var iterations = params.iterations;
                    var initialSolution = params.initialSolution// x
                    var targetEvaluation = params.targetEvaluation; // b (optional, if not provided, we will use 0)
                    var damping = params.damping || 0;
                    var useSylvester = params.useSylvester;
                    var maxIter = params.lsqrIterations || 100;


                    var act_mat_cond_num = 0;

                    var numRows=_sparseJacobian.getNumRows();
                    var vectorX = new Float64Array(initialSolution);
                    var vectorB = new Float64Array(numRows);

                    for (var i=0; i<numRows.length; i++){
                        vectorB[i]=0;
                    }
                    if (targetEvaluation && targetEvaluation.length==numRows){
                        for (var i=0; i<numRows; i++){
                            vectorB[i]=+targetEvaluation[i];
                        }
                    }

                    var vectorY = new Float64Array(numRows);
                    for (var i=0; i<numRows; i++){
                        vectorY[i]=0;
                    }
                    var vectorBMinusY = new Float64Array(numRows);
                    for (var i=0; i<numRows; i++){
                        vectorBMinusY[i]=0;
                    }
                    var vectorWorkX = new Float64Array(initialSolution.length);
                    for (var i=0; i<initialSolution.length; i++){
                        vectorWorkX[i]=0;
                    }
                    for (var iter = 0; iter < iterations; iter++) {
                        var evaluation = evaluate({
                            vectorX: vectorX,
                            vectorY: vectorY,
                            calculateDifferentials: true
                        });
//                        continue;
                        // F(x+d)=b
                        // F(x)=y
                        //
                        // F(x+d) ~= F(x)+F'(x)*d
                        // F(x)+F'(x)*d=b
                        // F'(x)*d=b-y
                        // Resolver sistema de arriba por LSQR
                        for (var i = 0, ic = vectorY.length; i < ic; i++) {
                            vectorBMinusY[i] = vectorB[i] - vectorY[i];
                        }

                        if (useSylvester) {
                            var matrix = _sparseJacobian.toSylvesterMatrix();
                            var b = sylvester.Vector.create(vectorBMinusY);


                            sylvester.solve_system(matrix, vectorWorkX, b);
                            for (var i = 0; i < vectorWorkX.length; i++) {
                                vectorX[i] += vectorWorkX[i];
                            }
                        } else {
                            var num_rows = _sparseJacobian.getNumRows();
                            var num_cols = _sparseJacobian.getNumCols();
                            _lsqr.allocLsqrMem();
                            _lsqr.input.rhs_vec = new Float64Array(vectorBMinusY);
                            _lsqr.input.sol_vec = new Float64Array(vectorX.length);
                            for (var i=0; i<vectorX.length; i++){
                                _lsqr.input.sol_vec[i]=0;
                            }
                            _lsqr.input.num_rows = num_rows;
                            _lsqr.input.num_cols = num_cols;
                            _lsqr.input.damp_val = damping;
                            _lsqr.input.rel_mat_err = 1.0e-10;
                            _lsqr.input.rel_rhs_err = 1.0e-10;
                            _lsqr.input.cond_lim = 10.0 * act_mat_cond_num;
                            _lsqr.input.max_iter = maxIter;
                            _lsqr.do_lsqr();
                            var sol_vec = _lsqr.output.sol_vec;

                            /* var matrix=_sparseJacobian.toSylvesterMatrix();
                             var b=sylvester.Vector.create(vectorBMinusY);
                             sylvester.solve_system(matrix,vectorWorkX,b);*/


                            for (var i = 0; i < sol_vec.length; i++) {
                                vectorX[i] += sol_vec[i];
                            }
                        }
                        /*
                         _lsqr.do_lsqr();
                         var sol_vec=_lsqr.output.sol_vec;
                         for (var i= 0,ic=sol_vec.length; i<ic; i++){
                         vectorX[i]+=sol_vec[i];
                         }*/
                    }
                    return vectorX;
                }


                return {
                    init: init, // params -> {constraints:[{type:integer,data:object,variables[integer]}]}
                    solve: solve
                }
            }

            return {
                newInstance: newInstance
            }
        }])
        .factory('sylvester', [function () {
            "use strict";

            // === Sylvester ===
// Vector and Matrix mathematics modules for JavaScript
// Copyright (c) 2007 James Coglan
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation
// the rights to use, copy, modify, merge, publish, distribute, sublicense,
// and/or sell copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
// OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.

            var Sylvester = {
                version: '0.1.3',
                precision: 1e-6
            };

            function Vector() {
            }

            Vector.prototype = {

                // Returns element i of the vector
                e: function (i) {
                    return (i < 1 || i > this.elements.length) ? null : this.elements[i - 1];
                },

                // Returns the number of elements the vector has
                dimensions: function () {
                    return this.elements.length;
                },

                // Returns the modulus ('length') of the vector
                modulus: function () {
                    return Math.sqrt(this.dot(this));
                },

                // Returns true iff the vector is equal to the argument
                eql: function (vector) {
                    var n = this.elements.length;
                    var V = vector.elements || vector;
                    if (n != V.length) {
                        return false;
                    }
                    do {
                        if (Math.abs(this.elements[n - 1] - V[n - 1]) > Sylvester.precision) {
                            return false;
                        }
                    } while (--n);
                    return true;
                },

                // Returns a copy of the vector
                dup: function () {
                    return Vector.create(this.elements);
                },

                // Maps the vector to another vector according to the given function
                map: function (fn) {
                    var elements = [];
                    this.each(function (x, i) {
                        elements.push(fn(x, i));
                    });
                    return Vector.create(elements);
                },

                // Calls the iterator for each element of the vector in turn
                each: function (fn) {
                    var n = this.elements.length, k = n, i;
                    do {
                        i = k - n;
                        fn(this.elements[i], i + 1);
                    } while (--n);
                },

                // Returns a new vector created by normalizing the receiver
                toUnitVector: function () {
                    var r = this.modulus();
                    if (r === 0) {
                        return this.dup();
                    }
                    return this.map(function (x) {
                        return x / r;
                    });
                },

                // Returns the angle between the vector and the argument (also a vector)
                angleFrom: function (vector) {
                    var V = vector.elements || vector;
                    var n = this.elements.length, k = n, i;
                    if (n != V.length) {
                        return null;
                    }
                    var dot = 0, mod1 = 0, mod2 = 0;
                    // Work things out in parallel to save time
                    this.each(function (x, i) {
                        dot += x * V[i - 1];
                        mod1 += x * x;
                        mod2 += V[i - 1] * V[i - 1];
                    });
                    mod1 = Math.sqrt(mod1);
                    mod2 = Math.sqrt(mod2);
                    if (mod1 * mod2 === 0) {
                        return null;
                    }
                    var theta = dot / (mod1 * mod2);
                    if (theta < -1) {
                        theta = -1;
                    }
                    if (theta > 1) {
                        theta = 1;
                    }
                    return Math.acos(theta);
                },

                // Returns true iff the vector is parallel to the argument
                isParallelTo: function (vector) {
                    var angle = this.angleFrom(vector);
                    return (angle === null) ? null : (angle <= Sylvester.precision);
                },

                // Returns true iff the vector is antiparallel to the argument
                isAntiparallelTo: function (vector) {
                    var angle = this.angleFrom(vector);
                    return (angle === null) ? null : (Math.abs(angle - Math.PI) <= Sylvester.precision);
                },

                // Returns true iff the vector is perpendicular to the argument
                isPerpendicularTo: function (vector) {
                    var dot = this.dot(vector);
                    return (dot === null) ? null : (Math.abs(dot) <= Sylvester.precision);
                },

                // Returns the result of adding the argument to the vector
                add: function (vector) {
                    var V = vector.elements || vector;
                    if (this.elements.length != V.length) {
                        return null;
                    }
                    return this.map(function (x, i) {
                        return x + V[i - 1];
                    });
                },

                // Returns the result of subtracting the argument from the vector
                subtract: function (vector) {
                    var V = vector.elements || vector;
                    if (this.elements.length != V.length) {
                        return null;
                    }
                    return this.map(function (x, i) {
                        return x - V[i - 1];
                    });
                },

                // Returns the result of multiplying the elements of the vector by the argument
                multiply: function (k) {
                    return this.map(function (x) {
                        return x * k;
                    });
                },

                x: function (k) {
                    return this.multiply(k);
                },

                // Returns the scalar product of the vector with the argument
                // Both vectors must have equal dimensionality
                dot: function (vector) {
                    var V = vector.elements || vector;
                    var i, product = 0, n = this.elements.length;
                    if (n != V.length) {
                        return null;
                    }
                    do {
                        product += this.elements[n - 1] * V[n - 1];
                    } while (--n);
                    return product;
                },

                // Returns the vector product of the vector with the argument
                // Both vectors must have dimensionality 3
                cross: function (vector) {
                    var B = vector.elements || vector;
                    if (this.elements.length != 3 || B.length != 3) {
                        return null;
                    }
                    var A = this.elements;
                    return Vector.create([
                        (A[1] * B[2]) - (A[2] * B[1]),
                        (A[2] * B[0]) - (A[0] * B[2]),
                        (A[0] * B[1]) - (A[1] * B[0])
                    ]);
                },

                // Returns the (absolute) largest element of the vector
                max: function () {
                    var m = 0, n = this.elements.length, k = n, i;
                    do {
                        i = k - n;
                        if (Math.abs(this.elements[i]) > Math.abs(m)) {
                            m = this.elements[i];
                        }
                    } while (--n);
                    return m;
                },

                // Returns the index of the first match found
                indexOf: function (x) {
                    var index = null, n = this.elements.length, k = n, i;
                    do {
                        i = k - n;
                        if (index === null && this.elements[i] == x) {
                            index = i + 1;
                        }
                    } while (--n);
                    return index;
                },

                // Returns a diagonal matrix with the vector's elements as its diagonal elements
                toDiagonalMatrix: function () {
                    return Matrix.Diagonal(this.elements);
                },

                // Returns the result of rounding the elements of the vector
                round: function () {
                    return this.map(function (x) {
                        return Math.round(x);
                    });
                },

                // Returns a copy of the vector with elements set to the given value if they
                // differ from it by less than Sylvester.precision
                snapTo: function (x) {
                    return this.map(function (y) {
                        return (Math.abs(y - x) <= Sylvester.precision) ? x : y;
                    });
                },

                // Returns the vector's distance from the argument, when considered as a point in space
                distanceFrom: function (obj) {
                    if (obj.anchor) {
                        return obj.distanceFrom(this);
                    }
                    var V = obj.elements || obj;
                    if (V.length != this.elements.length) {
                        return null;
                    }
                    var sum = 0, part;
                    this.each(function (x, i) {
                        part = x - V[i - 1];
                        sum += part * part;
                    });
                    return Math.sqrt(sum);
                },

                // Returns true if the vector is point on the given line
                liesOn: function (line) {
                    return line.contains(this);
                },

                // Return true iff the vector is a point in the given plane
                liesIn: function (plane) {
                    return plane.contains(this);
                },

                // Rotates the vector about the given object. The object should be a
                // point if the vector is 2D, and a line if it is 3D. Be careful with line directions!
                rotate: function (t, obj) {
                    var V, R, x, y, z;
                    switch (this.elements.length) {
                        case 2:
                            V = obj.elements || obj;
                            if (V.length != 2) {
                                return null;
                            }
                            R = Matrix.Rotation(t).elements;
                            x = this.elements[0] - V[0];
                            y = this.elements[1] - V[1];
                            return Vector.create([
                                V[0] + R[0][0] * x + R[0][1] * y,
                                V[1] + R[1][0] * x + R[1][1] * y
                            ]);
                            break;
                        case 3:
                            if (!obj.direction) {
                                return null;
                            }
                            var C = obj.pointClosestTo(this).elements;
                            R = Matrix.Rotation(t, obj.direction).elements;
                            x = this.elements[0] - C[0];
                            y = this.elements[1] - C[1];
                            z = this.elements[2] - C[2];
                            return Vector.create([
                                C[0] + R[0][0] * x + R[0][1] * y + R[0][2] * z,
                                C[1] + R[1][0] * x + R[1][1] * y + R[1][2] * z,
                                C[2] + R[2][0] * x + R[2][1] * y + R[2][2] * z
                            ]);
                            break;
                        default:
                            return null;
                    }
                },

                // Returns the result of reflecting the point in the given point, line or plane
                reflectionIn: function (obj) {
                    if (obj.anchor) {
                        // obj is a plane or line
                        var P = this.elements.slice();
                        var C = obj.pointClosestTo(P).elements;
                        return Vector.create([C[0] + (C[0] - P[0]), C[1] + (C[1] - P[1]), C[2] + (C[2] - (P[2] || 0))]);
                    } else {
                        // obj is a point
                        var Q = obj.elements || obj;
                        if (this.elements.length != Q.length) {
                            return null;
                        }
                        return this.map(function (x, i) {
                            return Q[i - 1] + (Q[i - 1] - x);
                        });
                    }
                },

                // Utility to make sure vectors are 3D. If they are 2D, a zero z-component is added
                to3D: function () {
                    var V = this.dup();
                    switch (V.elements.length) {
                        case 3:
                            break;
                        case 2:
                            V.elements.push(0);
                            break;
                        default:
                            return null;
                    }
                    return V;
                },

                // Returns a string representation of the vector
                inspect: function () {
                    return '[' + this.elements.join(', ') + ']';
                },

                // Set vector's elements from an array
                setElements: function (els) {
                    this.elements = (els.elements || els).slice();
                    return this;
                }
            };

// Constructor function
            Vector.create = function (elements) {
                var V = new Vector();
                return V.setElements(elements);
            };

// i, j, k unit vectors
            Vector.i = Vector.create([1, 0, 0]);
            Vector.j = Vector.create([0, 1, 0]);
            Vector.k = Vector.create([0, 0, 1]);

// Random vector of size n
            Vector.Random = function (n) {
                var elements = [];
                do {
                    elements.push(Math.random());
                } while (--n);
                return Vector.create(elements);
            };

// Vector filled with zeros
            Vector.Zero = function (n) {
                var elements = [];
                do {
                    elements.push(0);
                } while (--n);
                return Vector.create(elements);
            };


            function Matrix() {
            }

            Matrix.prototype = {

                // Returns element (i,j) of the matrix
                e: function (i, j) {
                    if (i < 1 || i > this.elements.length || j < 1 || j > this.elements[0].length) {
                        return null;
                    }
                    return this.elements[i - 1][j - 1];
                },

                // Returns row k of the matrix as a vector
                row: function (i) {
                    if (i > this.elements.length) {
                        return null;
                    }
                    return Vector.create(this.elements[i - 1]);
                },

                // Returns column k of the matrix as a vector
                col: function (j) {
                    if (j > this.elements[0].length) {
                        return null;
                    }
                    var col = [], n = this.elements.length, k = n, i;
                    do {
                        i = k - n;
                        col.push(this.elements[i][j - 1]);
                    } while (--n);
                    return Vector.create(col);
                },

                // Returns the number of rows/columns the matrix has
                dimensions: function () {
                    return {rows: this.elements.length, cols: this.elements[0].length};
                },

                // Returns the number of rows in the matrix
                rows: function () {
                    return this.elements.length;
                },

                // Returns the number of columns in the matrix
                cols: function () {
                    return this.elements[0].length;
                },

                // Returns true iff the matrix is equal to the argument. You can supply
                // a vector as the argument, in which case the receiver must be a
                // one-column matrix equal to the vector.
                eql: function (matrix) {
                    var M = matrix.elements || matrix;
                    if (typeof(M[0][0]) == 'undefined') {
                        M = Matrix.create(M).elements;
                    }
                    if (this.elements.length != M.length ||
                        this.elements[0].length != M[0].length) {
                        return false;
                    }
                    var ni = this.elements.length, ki = ni, i, nj, kj = this.elements[0].length, j;
                    do {
                        i = ki - ni;
                        nj = kj;
                        do {
                            j = kj - nj;
                            if (Math.abs(this.elements[i][j] - M[i][j]) > Sylvester.precision) {
                                return false;
                            }
                        } while (--nj);
                    } while (--ni);
                    return true;
                },

                // Returns a copy of the matrix
                dup: function () {
                    return Matrix.create(this.elements);
                },

                // Maps the matrix to another matrix (of the same dimensions) according to the given function
                map: function (fn) {
                    var els = [], ni = this.elements.length, ki = ni, i, nj, kj = this.elements[0].length, j;
                    do {
                        i = ki - ni;
                        nj = kj;
                        els[i] = [];
                        do {
                            j = kj - nj;
                            els[i][j] = fn(this.elements[i][j], i + 1, j + 1);
                        } while (--nj);
                    } while (--ni);
                    return Matrix.create(els);
                },

                // Returns true iff the argument has the same dimensions as the matrix
                isSameSizeAs: function (matrix) {
                    var M = matrix.elements || matrix;
                    if (typeof(M[0][0]) == 'undefined') {
                        M = Matrix.create(M).elements;
                    }
                    return (this.elements.length == M.length &&
                    this.elements[0].length == M[0].length);
                },

                // Returns the result of adding the argument to the matrix
                add: function (matrix) {
                    var M = matrix.elements || matrix;
                    if (typeof(M[0][0]) == 'undefined') {
                        M = Matrix.create(M).elements;
                    }
                    if (!this.isSameSizeAs(M)) {
                        return null;
                    }
                    return this.map(function (x, i, j) {
                        return x + M[i - 1][j - 1];
                    });
                },

                // Returns the result of subtracting the argument from the matrix
                subtract: function (matrix) {
                    var M = matrix.elements || matrix;
                    if (typeof(M[0][0]) == 'undefined') {
                        M = Matrix.create(M).elements;
                    }
                    if (!this.isSameSizeAs(M)) {
                        return null;
                    }
                    return this.map(function (x, i, j) {
                        return x - M[i - 1][j - 1];
                    });
                },

                // Returns true iff the matrix can multiply the argument from the left
                canMultiplyFromLeft: function (matrix) {
                    var M = matrix.elements || matrix;
                    if (typeof(M[0][0]) == 'undefined') {
                        M = Matrix.create(M).elements;
                    }
                    // this.columns should equal matrix.rows
                    return (this.elements[0].length == M.length);
                },

                // Returns the result of multiplying the matrix from the right by the argument.
                // If the argument is a scalar then just multiply all the elements. If the argument is
                // a vector, a vector is returned, which saves you having to remember calling
                // col(1) on the result.
                multiply: function (matrix) {
                    if (!matrix.elements) {
                        return this.map(function (x) {
                            return x * matrix;
                        });
                    }
                    var returnVector = matrix.modulus ? true : false;
                    var M = matrix.elements || matrix;
                    if (typeof(M[0][0]) == 'undefined') {
                        M = Matrix.create(M).elements;
                    }
                    if (!this.canMultiplyFromLeft(M)) {
                        return null;
                    }
                    var ni = this.elements.length, ki = ni, i, nj, kj = M[0].length, j;
                    var cols = this.elements[0].length, elements = [], sum, nc, c;
                    do {
                        i = ki - ni;
                        elements[i] = [];
                        nj = kj;
                        do {
                            j = kj - nj;
                            sum = 0;
                            nc = cols;
                            do {
                                c = cols - nc;
                                sum += this.elements[i][c] * M[c][j];
                            } while (--nc);
                            elements[i][j] = sum;
                        } while (--nj);
                    } while (--ni);
                    var M = Matrix.create(elements);
                    return returnVector ? M.col(1) : M;
                },

                x: function (matrix) {
                    return this.multiply(matrix);
                },

                // Returns a submatrix taken from the matrix
                // Argument order is: start row, start col, nrows, ncols
                // Element selection wraps if the required index is outside the matrix's bounds, so you could
                // use this to perform row/column cycling or copy-augmenting.
                minor: function (a, b, c, d) {
                    var elements = [], ni = c, i, nj, j;
                    var rows = this.elements.length, cols = this.elements[0].length;
                    do {
                        i = c - ni;
                        elements[i] = [];
                        nj = d;
                        do {
                            j = d - nj;
                            elements[i][j] = this.elements[(a + i - 1) % rows][(b + j - 1) % cols];
                        } while (--nj);
                    } while (--ni);
                    return Matrix.create(elements);
                },

                // Returns the transpose of the matrix
                transpose: function () {
                    var rows = this.elements.length, cols = this.elements[0].length;
                    var elements = [], ni = cols, i, nj, j;
                    do {
                        i = cols - ni;
                        elements[i] = [];
                        nj = rows;
                        do {
                            j = rows - nj;
                            elements[i][j] = this.elements[j][i];
                        } while (--nj);
                    } while (--ni);
                    return Matrix.create(elements);
                },

                // Returns true iff the matrix is square
                isSquare: function () {
                    return (this.elements.length == this.elements[0].length);
                },

                // Returns the (absolute) largest element of the matrix
                max: function () {
                    var m = 0, ni = this.elements.length, ki = ni, i, nj, kj = this.elements[0].length, j;
                    do {
                        i = ki - ni;
                        nj = kj;
                        do {
                            j = kj - nj;
                            if (Math.abs(this.elements[i][j]) > Math.abs(m)) {
                                m = this.elements[i][j];
                            }
                        } while (--nj);
                    } while (--ni);
                    return m;
                },

                // Returns the indeces of the first match found by reading row-by-row from left to right
                indexOf: function (x) {
                    var index = null, ni = this.elements.length, ki = ni, i, nj, kj = this.elements[0].length, j;
                    do {
                        i = ki - ni;
                        nj = kj;
                        do {
                            j = kj - nj;
                            if (this.elements[i][j] == x) {
                                return {i: i + 1, j: j + 1};
                            }
                        } while (--nj);
                    } while (--ni);
                    return null;
                },

                // If the matrix is square, returns the diagonal elements as a vector.
                // Otherwise, returns null.
                diagonal: function () {
                    if (!this.isSquare) {
                        return null;
                    }
                    var els = [], n = this.elements.length, k = n, i;
                    do {
                        i = k - n;
                        els.push(this.elements[i][i]);
                    } while (--n);
                    return Vector.create(els);
                },

                // Make the matrix upper (right) triangular by Gaussian elimination.
                // This method only adds multiples of rows to other rows. No rows are
                // scaled up or switched, and the determinant is preserved.
                toRightTriangular: function () {
                    var M = this.dup(), els;
                    var n = this.elements.length, k = n, i, np, kp = this.elements[0].length, p;
                    do {
                        i = k - n;
                        if (M.elements[i][i] == 0) {
                            for (var j = i + 1; j < k; j++) {
                                if (M.elements[j][i] != 0) {
                                    els = [];
                                    np = kp;
                                    do {
                                        p = kp - np;
                                        els.push(M.elements[i][p] + M.elements[j][p]);
                                    } while (--np);
                                    M.elements[i] = els;
                                    break;
                                }
                            }
                        }
                        if (M.elements[i][i] != 0) {
                            for (j = i + 1; j < k; j++) {
                                var multiplier = M.elements[j][i] / M.elements[i][i];
                                els = [];
                                np = kp;
                                do {
                                    p = kp - np;
                                    // Elements with column numbers up to an including the number
                                    // of the row that we're subtracting can safely be set straight to
                                    // zero, since that's the point of this routine and it avoids having
                                    // to loop over and correct rounding errors later
                                    els.push(p <= i ? 0 : M.elements[j][p] - M.elements[i][p] * multiplier);
                                } while (--np);
                                M.elements[j] = els;
                            }
                        }
                    } while (--n);
                    return M;
                },

                toUpperTriangular: function () {
                    return this.toRightTriangular();
                },

                // Returns the determinant for square matrices
                determinant: function () {
                    if (!this.isSquare()) {
                        return null;
                    }
                    var M = this.toRightTriangular();
                    var det = M.elements[0][0], n = M.elements.length - 1, k = n, i;
                    do {
                        i = k - n + 1;
                        det = det * M.elements[i][i];
                    } while (--n);
                    return det;
                },

                det: function () {
                    return this.determinant();
                },

                // Returns true iff the matrix is singular
                isSingular: function () {
                    return (this.isSquare() && this.determinant() === 0);
                },

                // Returns the trace for square matrices
                trace: function () {
                    if (!this.isSquare()) {
                        return null;
                    }
                    var tr = this.elements[0][0], n = this.elements.length - 1, k = n, i;
                    do {
                        i = k - n + 1;
                        tr += this.elements[i][i];
                    } while (--n);
                    return tr;
                },

                tr: function () {
                    return this.trace();
                },

                // Returns the rank of the matrix
                rank: function () {
                    var M = this.toRightTriangular(), rank = 0;
                    var ni = this.elements.length, ki = ni, i, nj, kj = this.elements[0].length, j;
                    do {
                        i = ki - ni;
                        nj = kj;
                        do {
                            j = kj - nj;
                            if (Math.abs(M.elements[i][j]) > Sylvester.precision) {
                                rank++;
                                break;
                            }
                        } while (--nj);
                    } while (--ni);
                    return rank;
                },

                rk: function () {
                    return this.rank();
                },

                // Returns the result of attaching the given argument to the right-hand side of the matrix
                augment: function (matrix) {
                    var M = matrix.elements || matrix;
                    if (typeof(M[0][0]) == 'undefined') {
                        M = Matrix.create(M).elements;
                    }
                    var T = this.dup(), cols = T.elements[0].length;
                    var ni = T.elements.length, ki = ni, i, nj, kj = M[0].length, j;
                    if (ni != M.length) {
                        return null;
                    }
                    do {
                        i = ki - ni;
                        nj = kj;
                        do {
                            j = kj - nj;
                            T.elements[i][cols + j] = M[i][j];
                        } while (--nj);
                    } while (--ni);
                    return T;
                },

                // Returns the inverse (if one exists) using Gauss-Jordan
                inverse: function () {
                    if (!this.isSquare() || this.isSingular()) {
                        return null;
                    }
                    var ni = this.elements.length, ki = ni, i, j;
                    var M = this.augment(Matrix.I(ni)).toRightTriangular();
                    var np, kp = M.elements[0].length, p, els, divisor;
                    var inverse_elements = [], new_element;
                    // Matrix is non-singular so there will be no zeros on the diagonal
                    // Cycle through rows from last to first
                    do {
                        i = ni - 1;
                        // First, normalise diagonal elements to 1
                        els = [];
                        np = kp;
                        inverse_elements[i] = [];
                        divisor = M.elements[i][i];
                        do {
                            p = kp - np;
                            new_element = M.elements[i][p] / divisor;
                            els.push(new_element);
                            // Shuffle of the current row of the right hand side into the results
                            // array as it will not be modified by later runs through this loop
                            if (p >= ki) {
                                inverse_elements[i].push(new_element);
                            }
                        } while (--np);
                        M.elements[i] = els;
                        // Then, subtract this row from those above it to
                        // give the identity matrix on the left hand side
                        for (j = 0; j < i; j++) {
                            els = [];
                            np = kp;
                            do {
                                p = kp - np;
                                els.push(M.elements[j][p] - M.elements[i][p] * M.elements[j][i]);
                            } while (--np);
                            M.elements[j] = els;
                        }
                    } while (--ni);
                    return Matrix.create(inverse_elements);
                },

                inv: function () {
                    return this.inverse();
                },

                // Returns the result of rounding all the elements
                round: function () {
                    return this.map(function (x) {
                        return Math.round(x);
                    });
                },

                // Returns a copy of the matrix with elements set to the given value if they
                // differ from it by less than Sylvester.precision
                snapTo: function (x) {
                    return this.map(function (p) {
                        return (Math.abs(p - x) <= Sylvester.precision) ? x : p;
                    });
                },

                // Returns a string representation of the matrix
                inspect: function () {
                    var matrix_rows = [];
                    var n = this.elements.length, k = n, i;
                    do {
                        i = k - n;
                        matrix_rows.push(Vector.create(this.elements[i]).inspect());
                    } while (--n);
                    return matrix_rows.join('\n');
                },

                // Set the matrix's elements from an array. If the argument passed
                // is a vector, the resulting matrix will be a single column.
                setElements: function (els) {
                    var i, elements = els.elements || els;
                    if (typeof(elements[0][0]) != 'undefined') {
                        var ni = elements.length, ki = ni, nj, kj, j;
                        this.elements = [];
                        do {
                            i = ki - ni;
                            nj = elements[i].length;
                            kj = nj;
                            this.elements[i] = [];
                            do {
                                j = kj - nj;
                                this.elements[i][j] = elements[i][j];
                            } while (--nj);
                        } while (--ni);
                        return this;
                    }
                    var n = elements.length, k = n;
                    this.elements = [];
                    do {
                        i = k - n;
                        this.elements.push([elements[i]]);
                    } while (--n);
                    return this;
                }
            };

// Constructor function
            Matrix.create = function (elements) {
                var M = new Matrix();
                return M.setElements(elements);
            };

// Identity matrix of size n
            Matrix.I = function (n) {
                var els = [], k = n, i, nj, j;
                do {
                    i = k - n;
                    els[i] = [];
                    nj = k;
                    do {
                        j = k - nj;
                        els[i][j] = (i == j) ? 1 : 0;
                    } while (--nj);
                } while (--n);
                return Matrix.create(els);
            };

// Diagonal matrix - all off-diagonal elements are zero
            Matrix.Diagonal = function (elements) {
                var n = elements.length, k = n, i;
                var M = Matrix.I(n);
                do {
                    i = k - n;
                    M.elements[i][i] = elements[i];
                } while (--n);
                return M;
            };

// Rotation matrix about some axis. If no axis is
// supplied, assume we're after a 2D transform
            Matrix.Rotation = function (theta, a) {
                if (!a) {
                    return Matrix.create([
                        [Math.cos(theta), -Math.sin(theta)],
                        [Math.sin(theta), Math.cos(theta)]
                    ]);
                }
                var axis = a.dup();
                if (axis.elements.length != 3) {
                    return null;
                }
                var mod = axis.modulus();
                var x = axis.elements[0] / mod, y = axis.elements[1] / mod, z = axis.elements[2] / mod;
                var s = Math.sin(theta), c = Math.cos(theta), t = 1 - c;
                // Formula derived here: http://www.gamedev.net/reference/articles/article1199.asp
                // That proof rotates the co-ordinate system so theta
                // becomes -theta and sin becomes -sin here.
                return Matrix.create([
                    [t * x * x + c, t * x * y - s * z, t * x * z + s * y],
                    [t * x * y + s * z, t * y * y + c, t * y * z - s * x],
                    [t * x * z - s * y, t * y * z + s * x, t * z * z + c]
                ]);
            };

// Special case rotations
            Matrix.RotationX = function (t) {
                var c = Math.cos(t), s = Math.sin(t);
                return Matrix.create([
                    [1, 0, 0],
                    [0, c, -s],
                    [0, s, c]
                ]);
            };
            Matrix.RotationY = function (t) {
                var c = Math.cos(t), s = Math.sin(t);
                return Matrix.create([
                    [c, 0, s],
                    [0, 1, 0],
                    [-s, 0, c]
                ]);
            };
            Matrix.RotationZ = function (t) {
                var c = Math.cos(t), s = Math.sin(t);
                return Matrix.create([
                    [c, -s, 0],
                    [s, c, 0],
                    [0, 0, 1]
                ]);
            };

// Random matrix of n rows, m columns
            Matrix.Random = function (n, m) {
                return Matrix.Zero(n, m).map(
                    function () {
                        return Math.random();
                    }
                );
            };

// Matrix filled with zeros
            Matrix.Zero = function (n, m) {
                var els = [], ni = n, i, nj, j;
                do {
                    i = n - ni;
                    els[i] = [];
                    nj = m;
                    do {
                        j = m - nj;
                        els[i][j] = 0;
                    } while (--nj);
                } while (--ni);
                return Matrix.create(els);
            };

            /**
             * Resuelve usando la pseudoinversa
             * @param M
             * @param a
             * @param b
             * @returns {number}
             */
            function solve_system(M, a, b) {

                var Mt,
                    MtM,
                    MtMI,
                    Mdag,
                    R;
                var res;
                if (M.cols() > M.rows()) {
                    console.log("ERROR: solve_system: matrix M has e more columns than rows\n");
                    return (-1);
                }

                Mt = M.transpose();
                // MtM = Mt * M
                MtM = Mt.multiply(M);
                if (MtM.elements.length==1){
                    MtMI=MtM;
                    MtMI.elements[0][0]=1/MtMI.elements[0][0];
                }else
                    MtMI = MtM.inverse();
                // Mdag = MtMI * Mt
                Mdag = MtMI.multiply(Mt);
                // a = Mdag * b;
                R = Mdag.multiply(b);
                for (var i = 0; i < R.elements.length; i++) {
                    a[i] = R.elements[i];
                }
                return Matrix.create(R.elements);
            }


            function Line() {
            }

            Line.prototype = {

                // Returns true if the argument occupies the same space as the line
                eql: function (line) {
                    return (this.isParallelTo(line) && this.contains(line.anchor));
                },

                // Returns a copy of the line
                dup: function () {
                    return Line.create(this.anchor, this.direction);
                },

                // Returns the result of translating the line by the given vector/array
                translate: function (vector) {
                    var V = vector.elements || vector;
                    return Line.create([
                        this.anchor.elements[0] + V[0],
                        this.anchor.elements[1] + V[1],
                        this.anchor.elements[2] + (V[2] || 0)
                    ], this.direction);
                },

                // Returns true if the line is parallel to the argument. Here, 'parallel to'
                // means that the argument's direction is either parallel or antiparallel to
                // the line's own direction. A line is parallel to a plane if the two do not
                // have a unique intersection.
                isParallelTo: function (obj) {
                    if (obj.normal) {
                        return obj.isParallelTo(this);
                    }
                    var theta = this.direction.angleFrom(obj.direction);
                    return (Math.abs(theta) <= Sylvester.precision || Math.abs(theta - Math.PI) <= Sylvester.precision);
                },

                // Returns the line's perpendicular distance from the argument,
                // which can be a point, a line or a plane
                distanceFrom: function (obj) {
                    if (obj.normal) {
                        return obj.distanceFrom(this);
                    }
                    if (obj.direction) {
                        // obj is a line
                        if (this.isParallelTo(obj)) {
                            return this.distanceFrom(obj.anchor);
                        }
                        var N = this.direction.cross(obj.direction).toUnitVector().elements;
                        var A = this.anchor.elements, B = obj.anchor.elements;
                        return Math.abs((A[0] - B[0]) * N[0] + (A[1] - B[1]) * N[1] + (A[2] - B[2]) * N[2]);
                    } else {
                        // obj is a point
                        var P = obj.elements || obj;
                        var A = this.anchor.elements, D = this.direction.elements;
                        var PA1 = P[0] - A[0], PA2 = P[1] - A[1], PA3 = (P[2] || 0) - A[2];
                        var modPA = Math.sqrt(PA1 * PA1 + PA2 * PA2 + PA3 * PA3);
                        if (modPA === 0) return 0;
                        // Assumes direction vector is normalized
                        var cosTheta = (PA1 * D[0] + PA2 * D[1] + PA3 * D[2]) / modPA;
                        var sin2 = 1 - cosTheta * cosTheta;
                        return Math.abs(modPA * Math.sqrt(sin2 < 0 ? 0 : sin2));
                    }
                },

                // Returns true iff the argument is a point on the line
                contains: function (point) {
                    var dist = this.distanceFrom(point);
                    return (dist !== null && dist <= Sylvester.precision);
                },

                // Returns true iff the line lies in the given plane
                liesIn: function (plane) {
                    return plane.contains(this);
                },

                // Returns true iff the line has a unique point of intersection with the argument
                intersects: function (obj) {
                    if (obj.normal) {
                        return obj.intersects(this);
                    }
                    return (!this.isParallelTo(obj) && this.distanceFrom(obj) <= Sylvester.precision);
                },

                // Returns the unique intersection point with the argument, if one exists
                intersectionWith: function (obj) {
                    if (obj.normal) {
                        return obj.intersectionWith(this);
                    }
                    if (!this.intersects(obj)) {
                        return null;
                    }
                    var P = this.anchor.elements, X = this.direction.elements,
                        Q = obj.anchor.elements, Y = obj.direction.elements;
                    var X1 = X[0], X2 = X[1], X3 = X[2], Y1 = Y[0], Y2 = Y[1], Y3 = Y[2];
                    var PsubQ1 = P[0] - Q[0], PsubQ2 = P[1] - Q[1], PsubQ3 = P[2] - Q[2];
                    var XdotQsubP = -X1 * PsubQ1 - X2 * PsubQ2 - X3 * PsubQ3;
                    var YdotPsubQ = Y1 * PsubQ1 + Y2 * PsubQ2 + Y3 * PsubQ3;
                    var XdotX = X1 * X1 + X2 * X2 + X3 * X3;
                    var YdotY = Y1 * Y1 + Y2 * Y2 + Y3 * Y3;
                    var XdotY = X1 * Y1 + X2 * Y2 + X3 * Y3;
                    var k = (XdotQsubP * YdotY / XdotX + XdotY * YdotPsubQ) / (YdotY - XdotY * XdotY);
                    return Vector.create([P[0] + k * X1, P[1] + k * X2, P[2] + k * X3]);
                },

                // Returns the point on the line that is closest to the given point or line
                pointClosestTo: function (obj) {
                    if (obj.direction) {
                        // obj is a line
                        if (this.intersects(obj)) {
                            return this.intersectionWith(obj);
                        }
                        if (this.isParallelTo(obj)) {
                            return null;
                        }
                        var D = this.direction.elements, E = obj.direction.elements;
                        var D1 = D[0], D2 = D[1], D3 = D[2], E1 = E[0], E2 = E[1], E3 = E[2];
                        // Create plane containing obj and the shared normal and intersect this with it
                        // Thank you: http://www.cgafaq.info/wiki/Line-line_distance
                        var x = (D3 * E1 - D1 * E3), y = (D1 * E2 - D2 * E1), z = (D2 * E3 - D3 * E2);
                        var N = Vector.create([x * E3 - y * E2, y * E1 - z * E3, z * E2 - x * E1]);
                        var P = Plane.create(obj.anchor, N);
                        return P.intersectionWith(this);
                    } else {
                        // obj is a point
                        var P = obj.elements || obj;
                        if (this.contains(P)) {
                            return Vector.create(P);
                        }
                        var A = this.anchor.elements, D = this.direction.elements;
                        var D1 = D[0], D2 = D[1], D3 = D[2], A1 = A[0], A2 = A[1], A3 = A[2];
                        var x = D1 * (P[1] - A2) - D2 * (P[0] - A1), y = D2 * ((P[2] || 0) - A3) - D3 * (P[1] - A2),
                            z = D3 * (P[0] - A1) - D1 * ((P[2] || 0) - A3);
                        var V = Vector.create([D2 * x - D3 * z, D3 * y - D1 * x, D1 * z - D2 * y]);
                        var k = this.distanceFrom(P) / V.modulus();
                        return Vector.create([
                            P[0] + V.elements[0] * k,
                            P[1] + V.elements[1] * k,
                            (P[2] || 0) + V.elements[2] * k
                        ]);
                    }
                },

                // Returns a copy of the line rotated by t radians about the given line. Works by
                // finding the argument's closest point to this line's anchor point (call this C) and
                // rotating the anchor about C. Also rotates the line's direction about the argument's.
                // Be careful with this - the rotation axis' direction affects the outcome!
                rotate: function (t, line) {
                    // If we're working in 2D
                    if (typeof(line.direction) == 'undefined') {
                        line = Line.create(line.to3D(), Vector.k);
                    }
                    var R = Matrix.Rotation(t, line.direction).elements;
                    var C = line.pointClosestTo(this.anchor).elements;
                    var A = this.anchor.elements, D = this.direction.elements;
                    var C1 = C[0], C2 = C[1], C3 = C[2], A1 = A[0], A2 = A[1], A3 = A[2];
                    var x = A1 - C1, y = A2 - C2, z = A3 - C3;
                    return Line.create([
                        C1 + R[0][0] * x + R[0][1] * y + R[0][2] * z,
                        C2 + R[1][0] * x + R[1][1] * y + R[1][2] * z,
                        C3 + R[2][0] * x + R[2][1] * y + R[2][2] * z
                    ], [
                        R[0][0] * D[0] + R[0][1] * D[1] + R[0][2] * D[2],
                        R[1][0] * D[0] + R[1][1] * D[1] + R[1][2] * D[2],
                        R[2][0] * D[0] + R[2][1] * D[1] + R[2][2] * D[2]
                    ]);
                },

                // Returns the line's reflection in the given point or line
                reflectionIn: function (obj) {
                    if (obj.normal) {
                        // obj is a plane
                        var A = this.anchor.elements, D = this.direction.elements;
                        var A1 = A[0], A2 = A[1], A3 = A[2], D1 = D[0], D2 = D[1], D3 = D[2];
                        var newA = this.anchor.reflectionIn(obj).elements;
                        // Add the line's direction vector to its anchor, then mirror that in the plane
                        var AD1 = A1 + D1, AD2 = A2 + D2, AD3 = A3 + D3;
                        var Q = obj.pointClosestTo([AD1, AD2, AD3]).elements;
                        var newD = [Q[0] + (Q[0] - AD1) - newA[0], Q[1] + (Q[1] - AD2) - newA[1], Q[2] + (Q[2] - AD3) - newA[2]];
                        return Line.create(newA, newD);
                    } else if (obj.direction) {
                        // obj is a line - reflection obtained by rotating PI radians about obj
                        return this.rotate(Math.PI, obj);
                    } else {
                        // obj is a point - just reflect the line's anchor in it
                        var P = obj.elements || obj;
                        return Line.create(this.anchor.reflectionIn([P[0], P[1], (P[2] || 0)]), this.direction);
                    }
                },

                // Set the line's anchor point and direction.
                setVectors: function (anchor, direction) {
                    // Need to do this so that line's properties are not
                    // references to the arguments passed in
                    anchor = Vector.create(anchor);
                    direction = Vector.create(direction);
                    if (anchor.elements.length == 2) {
                        anchor.elements.push(0);
                    }
                    if (direction.elements.length == 2) {
                        direction.elements.push(0);
                    }
                    if (anchor.elements.length > 3 || direction.elements.length > 3) {
                        return null;
                    }
                    var mod = direction.modulus();
                    if (mod === 0) {
                        return null;
                    }
                    this.anchor = anchor;
                    this.direction = Vector.create([
                        direction.elements[0] / mod,
                        direction.elements[1] / mod,
                        direction.elements[2] / mod
                    ]);
                    return this;
                }
            };


// Constructor function
            Line.create = function (anchor, direction) {
                var L = new Line();
                return L.setVectors(anchor, direction);
            };

// Axes
            Line.X = Line.create(Vector.Zero(3), Vector.i);
            Line.Y = Line.create(Vector.Zero(3), Vector.j);
            Line.Z = Line.create(Vector.Zero(3), Vector.k);


            function Plane() {
            }

            Plane.prototype = {

                // Returns true iff the plane occupies the same space as the argument
                eql: function (plane) {
                    return (this.contains(plane.anchor) && this.isParallelTo(plane));
                },

                // Returns a copy of the plane
                dup: function () {
                    return Plane.create(this.anchor, this.normal);
                },

                // Returns the result of translating the plane by the given vector
                translate: function (vector) {
                    var V = vector.elements || vector;
                    return Plane.create([
                        this.anchor.elements[0] + V[0],
                        this.anchor.elements[1] + V[1],
                        this.anchor.elements[2] + (V[2] || 0)
                    ], this.normal);
                },

                // Returns true iff the plane is parallel to the argument. Will return true
                // if the planes are equal, or if you give a line and it lies in the plane.
                isParallelTo: function (obj) {
                    var theta;
                    if (obj.normal) {
                        // obj is a plane
                        theta = this.normal.angleFrom(obj.normal);
                        return (Math.abs(theta) <= Sylvester.precision || Math.abs(Math.PI - theta) <= Sylvester.precision);
                    } else if (obj.direction) {
                        // obj is a line
                        return this.normal.isPerpendicularTo(obj.direction);
                    }
                    return null;
                },

                // Returns true iff the receiver is perpendicular to the argument
                isPerpendicularTo: function (plane) {
                    var theta = this.normal.angleFrom(plane.normal);
                    return (Math.abs(Math.PI / 2 - theta) <= Sylvester.precision);
                },

                // Returns the plane's distance from the given object (point, line or plane)
                distanceFrom: function (obj) {
                    if (this.intersects(obj) || this.contains(obj)) {
                        return 0;
                    }
                    if (obj.anchor) {
                        // obj is a plane or line
                        var A = this.anchor.elements, B = obj.anchor.elements, N = this.normal.elements;
                        return Math.abs((A[0] - B[0]) * N[0] + (A[1] - B[1]) * N[1] + (A[2] - B[2]) * N[2]);
                    } else {
                        // obj is a point
                        var P = obj.elements || obj;
                        var A = this.anchor.elements, N = this.normal.elements;
                        return Math.abs((A[0] - P[0]) * N[0] + (A[1] - P[1]) * N[1] + (A[2] - (P[2] || 0)) * N[2]);
                    }
                },

                // Returns true iff the plane contains the given point or line
                contains: function (obj) {
                    if (obj.normal) {
                        return null;
                    }
                    if (obj.direction) {
                        return (this.contains(obj.anchor) && this.contains(obj.anchor.add(obj.direction)));
                    } else {
                        var P = obj.elements || obj;
                        var A = this.anchor.elements, N = this.normal.elements;
                        var diff = Math.abs(N[0] * (A[0] - P[0]) + N[1] * (A[1] - P[1]) + N[2] * (A[2] - (P[2] || 0)));
                        return (diff <= Sylvester.precision);
                    }
                },

                // Returns true iff the plane has a unique point/line of intersection with the argument
                intersects: function (obj) {
                    if (typeof(obj.direction) == 'undefined' && typeof(obj.normal) == 'undefined') {
                        return null;
                    }
                    return !this.isParallelTo(obj);
                },

                // Returns the unique intersection with the argument, if one exists. The result
                // will be a vector if a line is supplied, and a line if a plane is supplied.
                intersectionWith: function (obj) {
                    if (!this.intersects(obj)) {
                        return null;
                    }
                    if (obj.direction) {
                        // obj is a line
                        var A = obj.anchor.elements, D = obj.direction.elements,
                            P = this.anchor.elements, N = this.normal.elements;
                        var multiplier = (N[0] * (P[0] - A[0]) + N[1] * (P[1] - A[1]) + N[2] * (P[2] - A[2])) / (N[0] * D[0] + N[1] * D[1] + N[2] * D[2]);
                        return Vector.create([A[0] + D[0] * multiplier, A[1] + D[1] * multiplier, A[2] + D[2] * multiplier]);
                    } else if (obj.normal) {
                        // obj is a plane
                        var direction = this.normal.cross(obj.normal).toUnitVector();
                        // To find an anchor point, we find one co-ordinate that has a value
                        // of zero somewhere on the intersection, and remember which one we picked
                        var N = this.normal.elements, A = this.anchor.elements,
                            O = obj.normal.elements, B = obj.anchor.elements;
                        var solver = Matrix.Zero(2, 2), i = 0;
                        while (solver.isSingular()) {
                            i++;
                            solver = Matrix.create([
                                [N[i % 3], N[(i + 1) % 3]],
                                [O[i % 3], O[(i + 1) % 3]]
                            ]);
                        }
                        // Then we solve the simultaneous equations in the remaining dimensions
                        var inverse = solver.inverse().elements;
                        var x = N[0] * A[0] + N[1] * A[1] + N[2] * A[2];
                        var y = O[0] * B[0] + O[1] * B[1] + O[2] * B[2];
                        var intersection = [
                            inverse[0][0] * x + inverse[0][1] * y,
                            inverse[1][0] * x + inverse[1][1] * y
                        ];
                        var anchor = [];
                        for (var j = 1; j <= 3; j++) {
                            // This formula picks the right element from intersection by
                            // cycling depending on which element we set to zero above
                            anchor.push((i == j) ? 0 : intersection[(j + (5 - i) % 3) % 3]);
                        }
                        return Line.create(anchor, direction);
                    }
                },

                // Returns the point in the plane closest to the given point
                pointClosestTo: function (point) {
                    var P = point.elements || point;
                    var A = this.anchor.elements, N = this.normal.elements;
                    var dot = (A[0] - P[0]) * N[0] + (A[1] - P[1]) * N[1] + (A[2] - (P[2] || 0)) * N[2];
                    return Vector.create([P[0] + N[0] * dot, P[1] + N[1] * dot, (P[2] || 0) + N[2] * dot]);
                },

                // Returns a copy of the plane, rotated by t radians about the given line
                // See notes on Line#rotate.
                rotate: function (t, line) {
                    var R = Matrix.Rotation(t, line.direction).elements;
                    var C = line.pointClosestTo(this.anchor).elements;
                    var A = this.anchor.elements, N = this.normal.elements;
                    var C1 = C[0], C2 = C[1], C3 = C[2], A1 = A[0], A2 = A[1], A3 = A[2];
                    var x = A1 - C1, y = A2 - C2, z = A3 - C3;
                    return Plane.create([
                        C1 + R[0][0] * x + R[0][1] * y + R[0][2] * z,
                        C2 + R[1][0] * x + R[1][1] * y + R[1][2] * z,
                        C3 + R[2][0] * x + R[2][1] * y + R[2][2] * z
                    ], [
                        R[0][0] * N[0] + R[0][1] * N[1] + R[0][2] * N[2],
                        R[1][0] * N[0] + R[1][1] * N[1] + R[1][2] * N[2],
                        R[2][0] * N[0] + R[2][1] * N[1] + R[2][2] * N[2]
                    ]);
                },

                // Returns the reflection of the plane in the given point, line or plane.
                reflectionIn: function (obj) {
                    if (obj.normal) {
                        // obj is a plane
                        var A = this.anchor.elements, N = this.normal.elements;
                        var A1 = A[0], A2 = A[1], A3 = A[2], N1 = N[0], N2 = N[1], N3 = N[2];
                        var newA = this.anchor.reflectionIn(obj).elements;
                        // Add the plane's normal to its anchor, then mirror that in the other plane
                        var AN1 = A1 + N1, AN2 = A2 + N2, AN3 = A3 + N3;
                        var Q = obj.pointClosestTo([AN1, AN2, AN3]).elements;
                        var newN = [Q[0] + (Q[0] - AN1) - newA[0], Q[1] + (Q[1] - AN2) - newA[1], Q[2] + (Q[2] - AN3) - newA[2]];
                        return Plane.create(newA, newN);
                    } else if (obj.direction) {
                        // obj is a line
                        return this.rotate(Math.PI, obj);
                    } else {
                        // obj is a point
                        var P = obj.elements || obj;
                        return Plane.create(this.anchor.reflectionIn([P[0], P[1], (P[2] || 0)]), this.normal);
                    }
                },

                // Sets the anchor point and normal to the plane. If three arguments are specified,
                // the normal is calculated by assuming the three points should lie in the same plane.
                // If only two are sepcified, the second is taken to be the normal. Normal vector is
                // normalised before storage.
                setVectors: function (anchor, v1, v2) {
                    anchor = Vector.create(anchor);
                    anchor = anchor.to3D();
                    if (anchor === null) {
                        return null;
                    }
                    v1 = Vector.create(v1);
                    v1 = v1.to3D();
                    if (v1 === null) {
                        return null;
                    }
                    if (typeof(v2) == 'undefined') {
                        v2 = null;
                    } else {
                        v2 = Vector.create(v2);
                        v2 = v2.to3D();
                        if (v2 === null) {
                            return null;
                        }
                    }
                    var A1 = anchor.elements[0], A2 = anchor.elements[1], A3 = anchor.elements[2];
                    var v11 = v1.elements[0], v12 = v1.elements[1], v13 = v1.elements[2];
                    var normal, mod;
                    if (v2 !== null) {
                        var v21 = v2.elements[0], v22 = v2.elements[1], v23 = v2.elements[2];
                        normal = Vector.create([
                            (v12 - A2) * (v23 - A3) - (v13 - A3) * (v22 - A2),
                            (v13 - A3) * (v21 - A1) - (v11 - A1) * (v23 - A3),
                            (v11 - A1) * (v22 - A2) - (v12 - A2) * (v21 - A1)
                        ]);
                        mod = normal.modulus();
                        if (mod === 0) {
                            return null;
                        }
                        normal = Vector.create([normal.elements[0] / mod, normal.elements[1] / mod, normal.elements[2] / mod]);
                    } else {
                        mod = Math.sqrt(v11 * v11 + v12 * v12 + v13 * v13);
                        if (mod === 0) {
                            return null;
                        }
                        normal = Vector.create([v1.elements[0] / mod, v1.elements[1] / mod, v1.elements[2] / mod]);
                    }
                    this.anchor = anchor;
                    this.normal = normal;
                    return this;
                }
            };

// Constructor function
            Plane.create = function (anchor, v1, v2) {
                var P = new Plane();
                return P.setVectors(anchor, v1, v2);
            };

// X-Y-Z planes
            Plane.XY = Plane.create(Vector.Zero(3), Vector.k);
            Plane.YZ = Plane.create(Vector.Zero(3), Vector.i);
            Plane.ZX = Plane.create(Vector.Zero(3), Vector.j);
            Plane.YX = Plane.XY;
            Plane.ZY = Plane.YZ;
            Plane.XZ = Plane.ZX;

// Utility functions
            var $V = Vector.create;
            var $M = Matrix.create;
            var $L = Line.create;
            var $P = Plane.create;

            return {
                Vector: Vector,
                Matrix: Matrix,
                Line: Line,
                Plane: Plane,
                solve_system: solve_system
            }

        }])
        .factory('sprintf', [function () {
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
        }])
        .factory('lsqr', ['sprintf', function (sprintf) {
            var DBL_EPSILON = 2.2204460492503131e-16;

            // Interface of IO functions
            var iface = {
                print: function () {
                    var output = arguments[0];
                    var arg2 = [];
                    for (var i = 1; i < arguments.length; i++) {
                        arg2.push(arguments[i]);
                    }
                    var str = sprintf.sprintf.apply(null, arg2);
                    if (output instanceof Array) {
                        output.push(str);
                    } else
                        console.log(str);
                }
            }


            // Private library functions
            {

                var max = function (a, b) {
                    return a > b ? a : b;
                }

                var sqr = function (val) {
                    // Note variable "casting" using +
                    val = +val;
                    return +(val * val);
                }

                var lsqr_error = function (msg, code) {
                    // We just throw an exception. Somebody will catch it, hopefully ;)
                    throw msg;
                }

                var alloc_lvec = function (count) {
                    var lng_vec = new Int32Array(count);
                    return lng_vec;
                }

                var free_lvec = function (vec) {
                    // Makes no sense in javascript, but we keep just in case we decide to use our own heap management in the future for
                    // asm.js
                };

                var alloc_dvec = function (count) {
                    var dbl_vec = new Float64Array(count);
                    for (var i=0; i<count;i++){
                        dbl_vec[i]=0;
                    }
                    return dbl_vec;
                }

                var free_dvec = function (vec) {
                    // Makes no sense in javascript
                }


                var dvec_norm2 = function (vec) {
                    var indx;
                    var l;
                    var norm = 0.0;

                    norm = 0.0;

                    for (indx = 0, l = vec.length; indx < l; indx++)
                        norm += sqr(vec[indx]);

                    return Math.sqrt(norm);
                }

                var dvec_scale = function (amount, vec) {
                    var indx;
                    var l;

                    for (indx = 0, l = vec.length; indx < l; indx++)
                        vec[indx] *= amount;

                    return;
                }

                var dvec_copy = function (src, dst) {
                    var indx;
                    var l = src.length;
                    for (indx = 0; indx < l; indx++)
                        dst[indx] = src[indx];
                }
            }


            // Initialization. Expects a model with the appropriate interface
            function newInstance(model) {
                var myModel = model;

                var input = {
                    num_rows: 0,
                    num_cols: 0,
                    damp_val: 0,
                    rel_mat_err: 0,
                    rel_rhs_err: 0,
                    cond_lim: 0,
                    max_iter: 0,
                    lsqr_fp_out: null,
                    rhs_vec: null,
                    sol_vec: null
                };
                var output = {
                    term_flag: 0,
                    num_iters: 0,
                    frob_mat_norm: 0,
                    mat_cond_num: 0,
                    resid_norm: 0,
                    mat_resid_norm: 0,
                    sol_norm: 0,
                    sol_vec: null,
                    std_err_vec: null
                };
                var work = {
                    bidiag_wrk_vec: undefined,
                    srch_dir_vec: undefined
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

                function do_lsqr() {

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

                    var outFile = input.lsqr_fp_out

                    if (outFile) {
                        iface.print(outFile, "  Least Squares Solution of A*x = b\n" +
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
                        iface.print(outFile, "\tISTOP = %3i\t\t\tITER = %9i\n" +
                            "|| A ||_F = %13.5e\tcond( A ) = %13.5e\n" +
                            "|| r ||_2 = %13.5e\t|| A^T r ||_2 = %13.5e\n" +
                            "|| b ||_2 = %13.5e\t|| x - x0 ||_2 = %13.5e\n\n",
                            output.term_flag, output.num_iters, output.frob_mat_norm,
                            output.mat_cond_num, output.resid_norm, output.mat_resid_norm,
                            bnorm, output.sol_norm);
                        iface.print(outFile, term_msg[output.term_flag]);
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
                        var faux=Math.sqrt(sqr(+rhobar) + sqr(+input.damp_val));
                        if (faux*faux>0.0){
                            cs1 = rhobar / faux;
                        }else
                            cs1=0;
                        faux=Math.sqrt(sqr(+rhobar) + sqr(+input.damp_val));
                        if (faux*faux>0.0){
                            sn1 = input.damp_val / faux;
                        }else{
                            sn1=0;
                        }


                        psi = sn1 * phibar;
                        phibar = cs1 * phibar;
                        /*
                         *     Use a plane rotation to eliminate the subdiagonal element (BETA)
                         *     of the lower-bidiagonal matrix, giving an upper-bidiagonal matrix.
                         */
                        rho = Math.sqrt(sqr(rhobar) + sqr(input.damp_val) + sqr(beta));
                        if (rho*rho>0.0){
                            cs = Math.sqrt(sqr(rhobar) + sqr(input.damp_val)) / rho;
                            sn = beta / rho;
                        }
                        else{
                            cs=0;
                            sn=0;
                        }


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
                            if (rho*rho>0.0){
                                output.sol_vec[indx] += (phi / rho) *work.srch_dir_vec[indx];

                                /* update the standard error estimates vector se */
                                output.std_err_vec[indx] += sqr((1.0 / rho) *work.srch_dir_vec[indx]);

                                /* accumulate this quantity to estimate condition number of A
                                 */
                                ddnorm += sqr((1.0 / rho) * work.srch_dir_vec[indx]);

                                /* update the search direction vector w */
                                work.srch_dir_vec[indx] =
                                    work.bidiag_wrk_vec[indx] -
                                    (theta / rho) * work.srch_dir_vec[indx];
                            }


                        }
                        /*
                         *     Use a plane rotation on the right to eliminate the super-diagonal element
                         *     (THETA) of the upper-bidiagonal matrix.  Then use the result to estimate
                         *     the solution norm || x ||.
                         */
                        delta = sn2 * rho;
                        gammabar = -cs2 * rho;
                        if (gammabar*gammabar>0.0){
                            zetabar = (phi - delta * zeta) / gammabar;
                        }
                        else
                            zetabar=0;

                        /* compute an estimate of the solution norm || x || */
                        output.sol_norm = Math.sqrt(xxnorm + sqr(zetabar));

                        gamma_ = Math.sqrt(sqr(gammabar) + sqr(theta));
                        if (gamma_*gamma_>0.0){
                            cs2 = gammabar / gamma_;
                            sn2 = theta / gamma_;
                            zeta = (phi - delta * zeta) / gamma_;
                        }else{
                            cs2=0;
                            sn2=0;
                            zeta=0;
                        }


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
                        if (bnorm*bnorm>0.0){
                            stop_crit_1 = output.resid_norm / bnorm;
                        }


                        stop_crit_2 = 0.0;
                        if (output.resid_norm > 0.0)
                            stop_crit_2 = output.mat_resid_norm / ( output.frob_mat_norm *output.resid_norm );
                        if (output.mat_cond_num){
                            stop_crit_3 = 1.0 / output.mat_cond_num;
                        }



                        if (bnorm){
                            resid_tol = input.rel_rhs_err + input.rel_mat_err *output.mat_resid_norm *output.sol_norm / bnorm;
                            resid_tol_mach = DBL_EPSILON + DBL_EPSILON * output.mat_resid_norm *output.sol_norm / bnorm;
                        }
                        else{
                            resid_tol=0;
                            resid_tol_mach=0;
                        }
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
                    if (temp*temp>0.0){
                        temp = output.resid_norm / Math.sqrt(temp);
                    }else{
                        temp=0;
                    }


                    for (indx = 0; indx < input.num_cols; indx++)
                        /* update the standard error estimates vector se */
                        output.std_err_vec[indx] = temp *Math.sqrt(output.std_err_vec[indx]);
                    /*
                     *  If statistics are printed at each iteration, print the statistics for the
                     *  stopping condition.
                     */
                    if (input.lsqr_fp_out) {
                        iface.print(outFile, "\n\tISTOP = %3i\t\t\tITER = %9i\n" +
                            "|| A ||_F = %13.5e\tcond( A ) = %13.5e\n" +
                            "|| r ||_2 = %13.5e\t|| A^T r ||_2 = %13.5e\n" +
                            "|| b ||_2 = %13.5e\t|| x - x0 ||_2 = %13.5e\n\n",
                            output.term_flag, output.num_iters, output.frob_mat_norm,
                            output.mat_cond_num, output.resid_norm, output.mat_resid_norm,
                            bnorm, output.sol_norm);
                        iface.print(outFile, term_msg[output.term_flag]);
                    }
                }


                return {
                    do_lsqr: do_lsqr,
                    allocLsqrMem: allocLsqrMem,
                    freeLsqrMem: freeLsqrMem,
                    input: input,
                    output: output,
                    work: work
                }

            }

            return {
                newInstance: newInstance
            }
        }])
})();

/*

 F(z)=b --> tengo que resolver z (no lo se)

 yo se

 F(x)=y

 digo que z=x+delta

 F(x+delta)=b

 F(x+delta) +- F(x)+F'(x)*delta

 F(z) = b

 F(x+delta) = b

 F(x)+F'(x)*delta = b

 y + F'(x)*delta = b

 F'(x)*delta=b-y

 // Dada una constraint, tengo dos funciones

 evaluate(solution) --> me devuelve el valor de la constraint para el vector solución
 targetValue --> Valor objetivo
 weight --> Constraint weight


 . . . . . . . . . . . . .

 . . . . ... . . .

 */
