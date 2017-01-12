function seeMod(m) {

  var heading = $('<div/>').addClass('title').text(m.mod)

  var binds = $('<div/>')
  jQuery.each(m.binds, function(ix,b) { binds.append(seeBinds(b,true)) })

  return $('<div/>').append(heading,binds)


  /* ------------------------------------------------------------ */

  function seeBinds(b,atTop) {
    var binds = $('<div/>').addClass('binding-group')

    jQuery.each(b.binds, function(ix,b) {
      var bind = $('<div/>').addClass('bind')
      if (atTop) {
        bind.addClass('top').append($('<a/>').attr('name',b.var.id))
      }

      if (b.terms) bind.append(kw('(' + b.terms + ')'))
      bind.append(seeBindVar(b.var))

      var eq    = kw('=')
      var ex    = nested(seeExpr(b.def))
      var dots  = switcher(eq,ex,atTop)
      bind.append(eq,ex,dots)

      binds.append(bind)
    })

    return b.rec ? $('<div/>').append(kw('rec'), nested(binds))
                 : binds
  }

  /* ------------------------------------------------------------ */

  function seeBindVar(x) {

    var d = $('<div/>')
           .addClass('var clickable')
           .text(x.name)
           .addClass(x.id)
           .hover(entry,exit)

    var infoBox = null

    d.click(function() {
      var c     = 'active-long'
      var nowOn = d.hasClass(c)
      $('.' + c).removeClass(c)

      if (nowOn) {
        $('#details-long').empty()
      } else {
        findAll().addClass(c)
        if (infoBox) $('#details-long').empty().append(infoBox.clone())
      }
    })

    if (x.info) { d.addClass('arg').attr('id',x.id)
                  infoBox = seeDetails(x.info) }


    function findAll() {
      var c = '.' + x.id
      return $(c + ',div:has(' + c + ')+.dots')
    }

    function entry() {
      if (infoBox) $('#details-short').append(infoBox)
      findAll().addClass('active')
    }
    function exit () {
      findAll().removeClass('active')
      $('#details-short').empty()
    }

    return d
  }

  /* ------------------------------------------------------------ */

  function seeDetails(info) {
    var d = $('<table/>').addClass('details')

    if (info.poly.length !== 0) {
      var vars = $('<td/>').attr('colspan','3').append(kw('forall'))
      jQuery.each(info.poly,function(ix,p) {
        vars.append($('<div/>').addClass('arg').text(p))
      })
      vars.append(kw('.'))
      d.append($('<tr/>').append(vars))
    }

    jQuery.each(info.args,function(ix,p) {
      d.append
      ( $('<tr/>').append
        ( $('<td/>').text(p.strict)
        , $('<td/>').text(p.use)
        , $('<td/>').append
          ( $('<div/>').addClass('arg').text(p.type)
          , rarr()
          )
        )
      )
    })

    d.append
    ( $('<tr>').append
       ( $('<td/>').attr('colspan','2').text(info.term)
       , $('<td/>').text(info.result)
       )
    )

    function opt(key,val,skipVal) {
      if (val == skipVal) return []
      return [ $('<span/>').text(val) ]
    }

    var use = info.usage
    d.append
    ( $('<tr/>').append($('<td/>').attr('colspan','3').append($('<hr/>')))
    , $('<tr/>').append
       ( $('<td/>').attr('colspan','3').append
         ( $('<dl/>').append
            ( opt('Call artity',use.callAr, '0')
            , opt('One shot', use.oneShot, '')
            , opt('Occurs',use.occ,'')
            , opt('Demand',use.demand,'')
            )
         )
       )
    )

    return d
  }


  function seeGlob(x) {
    return $('<a/>')
           .addClass('var')
           .attr('title', x.module)
           .attr('href', x.module + '.html#' + x.id)
           .text(x.name)
  }

  function seeVar(x) { return seeBindVar(x) }





  /* ------------------------------------------------------------ */

  function kw(x) { return $('<div/>').addClass('kw').text(x) }
  function rarr() { return $('<div/>').addClass('kw').html('&rarr;') }
  function larr() { return $('<div/>').addClass('kw').html('&larr;') }
  function lam() { return $('<div/>').addClass('kw lam').html('&lambda;') }

  function nested(x) { return $('<div/>').addClass('nested').append(x) }



  /* ------------------------------------------------------------ */

  function switcher(sep,ex,open) {
    var dots = $('<div/>').addClass('clickable dots').html('&hellip;')

    dots.click(function() {
      if (dots.hasClass('active-long'))
        $('.active-long').removeClass('active-long')

      ex.slideDown()
      dots.hide()
    })

    sep.addClass('clickable')
       .click(function() { ex.slideToggle(); dots.toggle() })

    if (open) { dots.hide() } else { ex.hide() }
    return dots
  }

  /* ------------------------------------------------------------ */

  function seeExpr(e,p) {

    switch(e.tag) {
      case 'Var': return $('<div/>').addClass('small expr')
                         .append(seeVar(e.var))

      case 'Glob': return $('<div/>').addClass('small expr')
                          .append(seeGlob(e.var))

      case 'Lit': return $('<div/>').addClass('small expr')
                         .append(seeLit(e.lit))

      case 'App':
        var d = $('<div/>').addClass('app small expr')
        d.append(seeExpr(e.fun))
        jQuery.each(e.args, function(i,a) { d.append(seeExpr(a,true)
                                             .addClass('app-arg')) })
        if (p) d.addClass('paren')
        return d

      case 'Lam':
        var d = $('<div/>')
                .addClass('big expr')
                .append( lam() )

        var b = nested(seeExpr(e.body))

        jQuery.each(e.args, function(ix,a) { d.append(seeBindVar(a)) })

        d.append(rarr(), b)

        if (p) d.addClass('paren')
        return d

      case 'Let':
        var d = $('<div/>')
                .addClass('big expr')
                .append(kw('let'),nested(seeBinds(e.defs))
                       ,kw('in'),nested(seeExpr(e.body)))
        if (p) d.addClass('paren')
        return d

      case 'Case':

        // Special case for cases that just evaluate
        if (e.alts.length === 1) {
          var alt = e.alts[0]

          var rhs = seeExpr(alt.rhs)

          var d = $('<div/>')
                  .addClass('big expr')
                  .append(kw('let!'))

          if (rhs.find('.' + e.val.id).length !== 0) {
            d.append(seeBindVar(e.val))
            if (alt.con.tag !== 'DEFAULT') d.append(kw('as'))
          }

          if (alt.con.tag !== 'DEFAULT') d.append(seeAltCon(alt.con))

          jQuery.each(alt.binds,function(ix,b) {
            var ms = rhs.find('.' + b.id)
            if (ms.length === 0) b.name = '_'
            d.append(seeBindVar(b))
          })

          d.append(kw('='), seeExpr(e.expr),kw('in'),$('<div/>').append(rhs))

          return d
        }

        // Normal multi-way case
        var b = $('<div/>').addClass('nested')
        jQuery.each(e.alts,function(ix,alt) { b.append(seeAlt(alt)) })

        var d = $('<div/>')
                .addClass('big expr')
                .append( kw('case'), seeExpr(e.expr) )

       if (b.find('.' + e.val.id).length !== 0)
         d.append(kw('as'), seeBindVar(e.val))

        d.append(kw('of'), b)

        if (p) d.addClass('paren')
        return d


      default: return seeError('Unknown expression')
    }

  }

  function seeLit(l) {
    return $('<div/>')
           .addClass('lit')
           .attr('title',l.type)
           .text(l.lit)
  }

  function seeAlt(a) {
    var d = $('<div/>')
            .addClass('alt')
            .append( seeAltCon(a.con) )
    var rhs = nested(seeExpr(a.rhs))
    jQuery.each(a.binds,function(i,b) {
      var ms = rhs.find('.' + b.id)
      if (ms.length === 0) b.name = '_'
      d.append(seeBindVar(b))
    })
    var arr = rarr()
    var dots = switcher(arr,rhs)
    d.append(arr,rhs,dots)
    return d
  }

  function seeAltCon(a) {
    switch(a.tag) {
      case 'DataAlt': return kw(a.con.name)
                             .attr('title',a.con.module)
      case 'LitAlt': return seeLit(a.lit)
      case 'DEFAULT': return kw('DEFAULT')
      default: return seeError('Unknown AltCon')
    }
  }

  function seeError(a) {
    return $('<div/>').addClass('error').text(a)
  }

}





