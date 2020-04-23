########################################################################################################################################
# Program OptICal - Optimal Item Calibration
# Pretesting of 2PL and 3PL items for achievement tests
# Algorithm from paper:
# Ul Hassan and Miller (2020). An exchange algorithm for optimal calibration of items in computerized achievement tests
#
# Code by Mahmood Ul Hassan and Frank Miller, 2019-2020 
# Version 1.4.0  (2020-04-23)
#
# Program tested mainly with 2-4 items to calibrate
########################################################################################################################################
  
########################################################################################################################################
# Initial starting design, 2PL, 3PL, or mixed 2/3PL model
# Based on asymptotic theorems in Ul Hassan and Miller (2020) and on heuristics
########################################################################################################################################
start.design <- function(t,ip){
  mod <- dim(ip)[2]   # number of columns in ip (if 2, then 2PL; if 3, then 3PL model or mixture)
  a   <- ip[,1]
  b   <- ip[,2]
  if (mod==3) { c <- ip[,3] }
  borderv <- sort(b,index.return=TRUE)$ix 
  xi  <- array(data=0,dim=length(t))
  k   <- length(b)   # number of items
  
  # find index where these conditions satisfied
  indx1 <- which(t <= -4)
  indx2 <- which(t > -4 & t <= 0)
  indx3 <- which(t > 0  & t <= 4)
  indx4 <- which(t > 4)
  
  if (mod==2){
    m <- which(a==min(a))
    # if 2 items have same minimal a, pick the one which has minimal b for low and maximal b for high abilities in case 2PL
    if(length(m)>1){
      eb  <- which.min(b[m])
      ma  <- m[eb]
      eb1 <- which.max(b[m])
      ma1 <- m[eb1]
    } else { ma <- ma1 <- m }
    xi[indx1] <- ma
  }
  if (mod==3 && max(is.na(c))==1){
    # item with less(a) at infinity.
    m  <- which(a==min(a))
    # if 2 items have same minimal a, pick the one which has maximal b for high abilities
    if(length(m)>1){
      eb1 <- which.max(b[m])
      ma1 <- m[eb1]
    } else { ma1 <- m }
  
    # 3pl item with less(b) at -infinity.
    l2  <- which(!is.na(c))
    b2  <- b[l2]
    mc1 <- l2[which.min(b2)]
    xi[indx1] <- mc1
  }
  if (mod==3 && max(is.na(c))==0){
    m <- which(a==min(a))
    # if 2 items have same minimal a, pick the one which has greater value for (1-c)*exp(a*b) for high abilities in case 3PL
    if(length(m)>1){
      d   <- (1-c)*exp(a*b)
      ma1 <- which.max(d[m])
    } else { ma1 <- which.min(a) }
    xi[indx1] <- which.min(b)
  }

  xi[indx2] <- borderv[ceiling((t[indx2]+4)/4*k)]
  xi[indx3] <- borderv[ceiling(t[indx3]/4*k)]
  xi[indx4] <- ma1
  xi
}

########################################################################################################################################
# Starting design based on the design calculated in previous inner loop
# Technically, translates interval boundaries (h1) to new grid and returns design xi
########################################################################################################################################
start.design1 <- function(t,h1){
  h  <- h1[,1]
  I  <- h1[,3]
  I1 <- h1[,4]
  xi <- array(data=0,dim=length(t))
  k  <- length(h)
  
  # find index where these condition satisfy
  indx1     <- which(t<=h[1])
  xi[indx1] <- I[1]
  for(i in 2:k){
    indx2     <- which(t>h[i-1] & t<=h[i])
    xi[indx2] <- I[i]
  }
  indx1     <- which(t>h[k])
  xi[indx1] <- I1[k]
  xi
}

########################################################################################################################################
# Calculate elements of information matrix at theta for given theta-vector t and k items with 
# parameter values in ip. Later we use this to calculate directional derivatives. 2PL or 3PL or mixed 2/3PL
########################################################################################################################################
crit <- function(t,ip){
  k   <- dim(ip)[1]   # number of items
  mod <- dim(ip)[2]   # number of columns in ip (if 2, then 2PL; if 3, then 3PL model)
  n   <- length(t)    # number of examinees
  x   <- (c(t[1],t)+c(t,t[n]))/2    # vector x is t[1], the middle between all t's, and t[n]; length is n+1
  a   <- ip[,1]
  b   <- ip[,2]
  if (mod==3){ c <- ip[,3] }

  if (mod==2 || max(is.na(c)==1)){
    f11 <- function(x,a,b){ (1/(1+exp(-a*(x-b))))*(1-(1/(1+exp(-a*(x-b)))))*(((x-b)^2)*dnorm(x)) }
    f12 <- function(x,a,b){ (1/(1+exp(-a*(x-b))))*(1-(1/(1+exp(-a*(x-b)))))*((-a*(x-b))*dnorm(x)) }
    f22 <- function(x,a,b){ (1/(1+exp(-a*(x-b))))*(1-(1/(1+exp(-a*(x-b)))))*(dnorm(x)*a^2) }
  }
  if (mod==3){ 
    f   <- function(x,a,b,c){ (c+(1-c)*(1/(1+exp(-a*(x-b)))))*(1-(c+(1-c)*(1/(1+exp(-a*(x-b))))))*dnorm(x) }
    fA  <- function(x,a,b,c){ (x-b)*((exp(a*(x-b)))/(c + exp(a*(x-b)))) }
    fB  <- function(x,a,b,c){ ((-a*(exp(a*(x-b))))/(c+ exp(a*(x-b)))) }
    fC  <- function(x,a,b,c){ ((1+(exp(a*(x-b))))/((1-c)*(c+ exp(a*(x-b))))) }
  
    a11 <- function(x,a,b,c){ f(x,a,b,c)*(fA(x,a,b,c))^2 }
    a22 <- function(x,a,b,c){ f(x,a,b,c)*(fB(x,a,b,c))^2 }
    a33 <- function(x,a,b,c){ f(x,a,b,c)*(fC(x,a,b,c))^2 }
  
    a12 <- function(x,a,b,c){ f(x,a,b,c)*(fA(x,a,b,c))*(fB(x,a,b,c)) }
    a13 <- function(x,a,b,c){ f(x,a,b,c)*(fA(x,a,b,c))*(fC(x,a,b,c)) }
    a23 <- function(x,a,b,c){ f(x,a,b,c)*(fB(x,a,b,c))*(fC(x,a,b,c)) }
  } 
  if (mod==2) { M <- array(data=NA, dim=c(2,2,k,n)) }
  if (mod==3) { M <- array(data=NA, dim=c(3,3,k,n)) }

  for(i in 1:k){
    for(j in 1:n){
      if (mod==2 || is.na(c[i])){
        M11 <- integrate(f11,a[i],b[i],lower=x[j],upper=x[j+1])$value
        M12 <- integrate(f12,a[i],b[i],lower=x[j],upper=x[j+1])$value
        M22 <- integrate(f22,a[i],b[i],lower=x[j],upper=x[j+1])$value
        if (mod==3){ M13 <- M23 <- M33 <- NA }
      }
      if (mod==3 && !is.na(c[i])){
        M11 <- integrate(a11,a[i],b[i],c[i],lower=x[j],upper=x[j+1])$value
        M12 <- integrate(a12,a[i],b[i],c[i],lower=x[j],upper=x[j+1])$value
        M13 <- integrate(a13,a[i],b[i],c[i],lower=x[j],upper=x[j+1])$value
        M22 <- integrate(a22,a[i],b[i],c[i],lower=x[j],upper=x[j+1])$value
        M23 <- integrate(a23,a[i],b[i],c[i],lower=x[j],upper=x[j+1])$value
        M33 <- integrate(a33,a[i],b[i],c[i],lower=x[j],upper=x[j+1])$value
      }
      if (mod==2){ M[,,i,j] <- matrix(c(M11,M12,M12,M22),2,2) }
      if (mod==3){ M[,,i,j] <- matrix(c(M11,M12,M13,M12,M22,M23,M13,M23,M33),3,3,byrow=T) }
    }}
  M
}

########################################################################################################################################
# Function to calculate optimality critera of multiple designs xii
########################################################################################################################################
ocritmult <- function(M,xii){
  h <- dim(xii)[1] # number of designs compared
  k <- dim(M)[3]   # number of items
  logdetMinv <- rep(0,h)
  
  for (m in 1:h)
  {
    for (i in 1:k)
    {
      MF   <- M[,,i,(xii[m, ]== i)]
      smat <- apply(MF, MARGIN=c(1, 2), sum)
      if (dim(smat)[1]>2 && is.na(smat[3,3])){ dsmat <- det(smat[1:2,1:2]) } else { dsmat <- det(smat) }
      logdetMinv[m] <- logdetMinv[m] - log(dsmat)
    }
  }
  logdetMinv  
}

########################################################################################################################################
# Function to calculate optimality criterion of design xi
########################################################################################################################################
ocrit <- function(M,xi){
  k <- dim(M)[3]   # number of items
  logdetMinv <- 0
  for (i in 1:k)
  {
    MF   <- M[,,i,(xi==i)]
    smat <- apply(MF, MARGIN=c(1, 2), sum)
    if (dim(smat)[1]>2 && is.na(smat[3,3])){ dsmat <- det(smat[1:2,1:2]) } else { dsmat <- det(smat) }
    logdetMinv <- logdetMinv - log(dsmat)
  }
  logdetMinv  
}

########################################################################################################################################
# Function to calculate optimality criterion of random design
########################################################################################################################################
ocritr <- function(M){
  k <- dim(M)[3]
  logdetMinv <- 0
  for (i in 1:k)
  {
    MF   <- M[,,i,]
    smat <- apply(MF, MARGIN=c(1, 2), sum)/k
    if (dim(smat)[1]>2 && is.na(smat[3,3])){ dsmat <- det(smat[1:2,1:2]) } else { dsmat <- det(smat) }
    logdetMinv <- logdetMinv - log(dsmat)
  }
  logdetMinv
}

########################################################################################################################################
# Function to calculate directional derivative for design xi, 2PL or 3PL or mixed 2/3PL
########################################################################################################################################
ddriv <- function(M,xi,ip,t){
  k   <- dim(ip)[1]                # number of items
  mod <- dim(ip)[2]                # number of columns in ip (if 2, then 2PL; if 3, then 3PL model)
  n   <- length(t)                 # number of thetas in grid
  np  <- length(which(!is.na(ip))) # number of parameters
  dd  <- array(dim=c(k,n))
  a   <- ip[,1]
  b   <- ip[,2]
  if (mod==3){ 
    c <- ip[,3]
    # derivatives for 3PL model
    fA <- function(x,a,b,c){(x-b)*((exp(a*(x-b)))/(c + exp(a*(x-b))))}
    fB <- function(x,a,b,c){((-a*(exp(a*(x-b))))/(c + exp(a*(x-b))))}
    fC <- function(x,a,b,c){((1+(exp(a*(x-b))))/((1-c)*(c + exp(a*(x-b)))))}
    FL <- function(x,a,b,c)(c + ((1 - c)/(1 + exp(-a*(x-b)))))
  }
  
  for (i in 1:k){
    if (mod==3 && is.na(c[i])){ ar1 <- M[1:2,1:2,i,(xi==i)] } else { ar1 <- M[,,i,(xi==i)] }
    Minv <- solve(apply(ar1, MARGIN=c(1, 2), sum))
    for (j in 1:n){
      # directional derivatives dd[i,j] for item i at theta_j
      if (mod==2 || is.na(c[i])){
        dd[i,j] <- np - 1/(1+exp(-a[i]*(t[j]-b[i]))) * (1-1/(1+exp(-a[i]*(t[j]-b[i])))) * c(t[j]-b[i],-a[i]) %*% Minv %*% c(t[j]-b[i],-a[i])
      }
      else{
        fABC    <- c(fA(t[j],a[i],b[i],c[i]),fB(t[j],a[i],b[i],c[i]),fC(t[j],a[i],b[i],c[i]))
        dd[i,j] <- np - FL(t[j],a[i],b[i],c[i])*(1-FL(t[j],a[i],b[i],c[i])) * (t(fABC) %*% Minv %*% fABC)
      }
    }
  }
  dd
}

########################################################################################################################################
# Identify worst violation of equivalence theorem
########################################################################################################################################
idwv <- function(dd,xi){
  n      <- dim(dd)[2]
  ddmin  <- array(dim=n)
  ddamin <- array(dim=n)
  vio    <- array(dim=n)
  
  for (j in 1:n){
    ddmin[j]  <- min(dd[,j])
    ddamin[j] <- which.min(dd[,j])
    vio[j]    <- dd[xi[j],j] - ddmin[j]
  }
  list(ddmin=ddmin,ddamin=ddamin,vio=vio)
}

########################################################################################################################################
# Improve design 
########################################################################################################################################
impdesign <- function(viomax,vio,imf,xii,xi,ddamin,dd,t,k){
  li <- length(imf)   
  n  <- length(xi)
  
  for (m in 1:li){
    for (j in 1:n){ 
      if (vio[j]>(1-imf[m])*viomax)
      { 
        # change sampling to other item
        xii[m,j] <- ddamin[j]
      }
      else { xii[m,j] <- xi[j] }
    }
  }
  list(xii=xii)
}

########################################################################################################################################
# Compute interval boundaries
# Structure of result: (interval boundary, probability from last interval 
# boundary, item # sampled here, item # sampled next)
# Note that order of the 4 columns was different in earlier versions of the code
########################################################################################################################################
intbounds <- function(xi,t){
  ibold  <- -100
  n      <- length(t)
  bounds <- c()
  for (j in 2:n)
  {
    if (xi[j]!=xi[j-1]){
      ib     <- (t[j]+t[j-1])/2
      bound  <- c(ib,pnorm(ib)-pnorm(ibold),xi[j-1],xi[j])
      bounds <- rbind(bounds,bound)
      ibold  <- ib}
  }
  bound  <- c(100,1-pnorm(ibold),xi[n],xi[n])
  bounds <- rbind(bounds,bound)
  bounds
}

########################################################################################################################################
# Inner loop for optimization (results for interval bounds), using functions above
# xi     = starting design
# sss    = step size stopping criterion
# falpha = factor alpha for adjusting the step size vector
# sdr    = stop if design repeated (flag TRUE/FALSE)
########################################################################################################################################
innerloop <- function(t,ip,imf,maxiter=1000,eps=0.001,sss=0.0001,falpha=1.08,sdr=TRUE,xi){
  n   <- length(t)      # number of different ability levels (grid size)
  k   <- dim(ip)[1]     # number of items
  mod <- dim(ip)[2]     # number of columns in ip (if 2, then 2PL; if 3, then 3PL model)
  np  <- length(which(!is.na(ip))) # number of parameters
  li  <- length(imf)    # number of different designs compared in parallel (K in paper) 
  
  xii <- array(dim=c(li,n)) # matrix li*n 
  xii[1,] <- xi
  
  # calculate elements of matrix at each ability point: required to calculate directional derivative and criterion log(det(M^-1))  
  M <- crit(t,ip)
  logdetMinvRand <- ocritr(M)  # criterion of random design

  iterc  <- 0           # iteration counter
  viomax <- 999999      # initialisation of largest violation of equivalence theorem
  circle <- FALSE       # flag if iteration went into a loop (circular)
  effi   <- c()         # vector for efficiencies in each iteration
  lvio   <- c()         # vector of largest violations of equivalence theorem
  vss    <- c()         # vector of step-lengths used
  vssmin <- c() 
  vssmax <- c()
  while(viomax>eps & iterc<maxiter & imf[li]>sss & circle==FALSE){
    iterc <- iterc + 1
    
    logdetMinv <- ocritmult(M,xii) # calculate the log(det(M^-1)) for given position of item on theta
    mm <- which.min(logdetMinv)
    
    if (iterc>1 && mm==1)                  imf <- imf/falpha   # reduce step sizes if smallest step size was used
    if (iterc>1 && mm==li && imf[li]<0.5)  imf <- imf*falpha   # increase step sizes if largest step size was used

    # calculation of directional derivative
    xi <- xii[mm,]
    dd <- ddriv(M,xi,ip,t)

    tt <- idwv(dd,xi)
    # identification of violation of equivalence theorem
    ddmin  <- tt$ddmin
    ddamin <- tt$ddamin
    vio    <- tt$vio

    viomax <- max(vio)
    effi   <- c(effi,exp(logdetMinvRand-ocrit(M,xi))^(1/np))
    lvio   <- c(lvio,viomax)
    vss    <- c(vss,imf[mm])
    vssmin <- c(vssmin,imf[1])
    vssmax <- c(vssmax,imf[li])
    print(paste(iterc," logDetM^-1=",round(logdetMinv[mm],5)," MV=",round(viomax,7)," SS=",round(imf[mm],7)))
    
    if (sdr==TRUE){
      if (iterc>16 && min(xi==xiold)==1) { circle <- TRUE }    # if design is the same as saved in last of iteration 8, 16, 24, ... then stop
      if (iterc %% 8 == 0) { xiold <- xi }                     # save results every 8th iteration to check later circulation
    }

    idd  <- impdesign(viomax,vio,imf,xii,xi,ddamin,dd,t,k)     # improve design
    xii  <- idd$xii
  }
  # Matrix to monitor iterations
  moiter <- cbind(1:length(effi),effi,lvio,vss,vssmin,vssmax)

  list(dd=dd,xi=xi,viomax=viomax,moiter=moiter)
}

########################################################################################################################################
# Final graph to draw the (optimal) design; four layouts possible
# All layouts have design first incl. efficiency vs. random design; then line with item having minimal directional derivative
# Layout 1: third panel has directional derivatives (cut at ylowl or lowest value of dirdev)
# Layout 2: third panel has violations of equivalence theorem, should be ideally small. Stopping criterion could be <0.002 (refline)
# Layout 3: third panel monitors efficiency of design vs. iteration number
# Layout 4: third panel monitors violations of equivalence theorem vs. iteration number
# Layout 0: only one panel with design
# If textout==TRUE, the item parameters will be printed for m<5 and the efficiency vs. the random design
########################################################################################################################################
drawdesign <- function(yyy, ip, ylowl=-9999999, refline=0.002, textout=TRUE, itemnum=NA, layout=1){
  imd <- apply(yyy$dd,2,which.min)      # indicator for minimal directional derivative
  m   <- dim(ip)[1]                     # number of items
  if (is.na(itemnum[1])) itemnum <- 1:m
  mod <- dim(ip)[2]                     # number of columns in ip (if 2, then 2PL; if 3, then 3PL model)
  np  <- length(which(!is.na(ip)))      # number of parameters
  h   <- rbind(c(-8,0,0,0),yyy$h1)
  k   <- dim(h)[1]                      # number of intervals to be drawn + 1
  moo <- yyy$mooiter                    # monitored iterations
  z1  <- h[,1]
  z2  <- h[,3]
  
  if (layout>0) oldpar <- par(oma=c(1,1,0,1), mar=c(2,3,0.5,0), fig=c(0,1,0.53,1))  # for combined graph
           else oldpar <- par(oma=c(1,1,0,1), mar=c(2,3,0.5,0))

  # Normal distribution plot (Plot 1)
  x11 <- seq(-7,7,length=1001)
  y11 <- dnorm(x11)
  plot(x11,y11,type="l",lwd=1,axes=FALSE,xlab="",ylab="")
  axis(side=1,tick=TRUE,labels=FALSE,at=seq(-7,7, by=1))
  mtext("Ability",side=1,line=0.53,cex=1.2)
  
  # intervals filled with colours
  for(i in 2:k){
    cord.x1 <- c(z1[i-1],seq(z1[i-1],z1[i],0.001),z1[i]) 
    cord.y1 <- c(-0.02,dnorm(seq(z1[i-1],z1[i],0.001)),-0.02) 
    polygon(cord.x1,cord.y1,col=z2[i],border = NA,lend=1)
  }
  
  # labeling of all colours in plot
  if (m<5 && textout){ 
    if (mod==2) { ln<-c(paste0("Item ", itemnum, " (a=", round(ip[,1],3), ",\n", "b=", round(ip[,2],3), ")\n")) }
    if (mod==3) { ln<-c(paste0("Item ", itemnum, " (a=", round(ip[,1],3), ",\n", "b=", round(ip[,2],3), ", c=", round(ip[,3],3), ")\n")) }
  }  
  else { ln<-c(paste0("Item ", itemnum)) }
  legend("topleft",box.lty=0,inset=.005,ln, col=1:m,lwd=4,cex=0.95,horiz=FALSE,adj=c(0, 0.4))

  # Efficiency versus random design
  ti   <- length(moo[,1])
  effi <- moo[ti,3]
  if (textout) legend("topright",legend=paste0("Efficiency vs.\n", "random design = ",round(effi,3)),box.lty=0,cex=0.95)
  
  if (layout>0){
    par(fig=c(0,1,0.48,0.52), oma=c(0,1,0,1), mar=c(0,3,0,0), new=T)
    #draw the interval based on where dd are minimum (Plot 2)
    p <- length(imd)
    x <- cbind(yyy$t,imd)
    u <- rbind(c(-8,0),x,c(8,imd[p]))
    plot(c(-7,7),c(-0.1,0.1),type="n",axes=FALSE)
    for (i in 2:dim(u)[1]) { lines(c(u[(i-1),1],u[i,1]),c(0,0),col=u[i,2],lend=1,lwd=8) }

    par(fig=c(0,1,0,0.47), oma=c(1,1,0,1), mar=c(2,3,0.5,0), new=T)
    # Plot 3
    if (layout==1){
      #directional derivative plot box
      plot(c(-7,7),c(max(ylowl,min(yyy$dd)),np+0.5),type="n",axes=FALSE)
      axis(side=1,tick=TRUE,labels=T,at=seq(-7,7, by=1),cex.axis=1.2)
      axis(side=2,tick=TRUE,cex.axis=1.2)
      mtext("Directional derivative",side=2,line=2.3,cex=1.2)

      #draw directional derivative lines
      for (i in 1:m){lines(yyy$t,yyy$dd[i,],col=i,lwd=2)}
    }
    if (layout==2){
      viol <- idwv(yyy$dd,yyy$xi)$vio
      plot(c(-7,7),c(max(max(viol),refline)*1.1,0),type="n",axes=FALSE)
      axis(side=1,tick=TRUE,labels=T,at=seq(-7,7, by=1),cex.axis=1.2)
      axis(side=2,tick=TRUE,cex.axis=1.2)
      mtext("Violation of eq.th.",side=2,line=2.3,cex=1.2)
      points(yyy$t, viol, col=yyy$xi)
      abline(h=refline,col=2)
    }
    if (layout == 3){
      nil <- c()   # number of iteration when new inner loop (nil) begins
      for (i in 2:ti){
        if (moo[i-1,1]<moo[i,1]) { nil <- c(nil,i-0.5) }
      }
      tis <- min(ti/3,51)  # change the y-axis such that all results from iteration 51 are visible (or from total iterations/3 if earlier) 
      plot(c(1,ti),c(min(moo[tis:ti,3]),max(moo[,3])),type="n",xlab="Iteration number",axes=FALSE)
      axis(side=1,tick=TRUE,labels=T,cex.axis=1.2)
      axis(side=2,tick=TRUE,cex.axis=1.2)
      mtext("Iteration number",side=1,line=-1.0,cex=1.2)
      mtext("Efficiency (vs. random design)",side=2,line=2.3,cex=1.2)
      lines(1:ti,moo[,3],col=moo[,1],lwd=2)
      abline(v=nil,lty=2)
    }
    if (layout == 4){
      nil <- c()   # number of iteration when new inner loop (nil) begins
      for (i in 2:ti){
        if (moo[i-1,1]<moo[i,1]) { nil <- c(nil,i-0.5) }
      }
      moo[(moo[,4]<min(refline)/100),4] <- min(refline)/100
      plot(c(1,ti),c(min(c(moo[,4],0.001)),max(moo[3:ti,4])),type="n",xlab="Iteration number",ylab="Violation",log="y",axes=FALSE)
      axis(side=1,tick=TRUE,labels=T,cex.axis=1.2)
      axis(side=2,tick=TRUE,at=c(0.001,0.1,10,1000),cex.axis=1.2)
      mtext("Iteration number",side=1,line=-1.0,cex=1.2)
      mtext("Violation of eq.th.",side=2,line=2.3,cex=1.2)
      lines(1:ti,moo[,4],col=moo[,1],lwd=2)
      abline(v=nil,lty=2)
      abline(h=refline,lty=2)
    }
  }
  par(oldpar)  # reset graphical parameters
}

########################################################################################################################################
# Convergence plots
# First panel monitors efficiency of design vs. iteration number
# Second panel monitors violations of equivalence theorem vs. iteration number
# Maybe add following in future verions:
#   Third panel monitors alpha vs. iteration number
#   Fourth panel shows final grid
########################################################################################################################################
convergenceplot <- function(moo,refline=c(0.002,0.00001)){
  
  oldpar <- par(mfrow=c(3,1), oma=c(1,1,0,1), mar=c(2,3,0.5,0))  # for combined graph

  ti  <- length(moo[,1])  # total number of iterations
  nil <- c()              # number of iteration when new inner loop (nil) begins
  for (i in 2:ti){
    if (moo[i-1,1]<moo[i,1]) { nil <- c(nil,i-0.5) }
  }

  # Panel 1
    tis <- min(ti/3,51)  # change the y-axis such that all results from iteration 51 are visible (or from total iterations/3 if earlier) 
    plot(c(1,ti),c(min(moo[tis:ti,3]),max(moo[,3])),type="n",xlab="",ylab="",axes=FALSE)
    axis(side=1,tick=TRUE,labels=T,cex.axis=1.2)
    axis(side=2,tick=TRUE,cex.axis=1.2)
    #mtext("Iteration number",side=1,line=-1.0,cex=1.1)
    mtext("Efficiency (vs. rand.des)",side=2,line=2.3,cex=1.1)
    lines(1:ti,moo[,3],col=moo[,1],lwd=2)
    abline(v=nil,lty=2)

  # Panel 2
    plot(c(1,ti),c(min(c(moo[,4],0.001)),max(moo[3:ti,4])),type="n",log="y",xlab="",ylab="",axes=FALSE)
    axis(side=1,tick=TRUE,labels=T,cex.axis=1.2)
    axis(side=2,tick=TRUE,at=c(0.001,0.1,10,1000),cex.axis=1.2)
    #mtext("Iteration number",side=1,line=-1.0,cex=1.1)
    mtext("Violation of eq.th.",side=2,line=2.3,cex=1.1)
    lines(1:ti,moo[,4],col=moo[,1],lwd=2)
    abline(v=nil,lty=2)
    abline(h=refline[1],lty=2)

  # Panel 3
    plot(c(1,ti),c(min(c(moo[,5],0.001)),max(moo[,5])),type="n",log="y",xlab="",ylab="",axes=FALSE)
    axis(side=1,tick=TRUE,labels=T,cex.axis=1.2)
    axis(side=2,tick=TRUE,at=c(0.001,0.01,0.1,1),cex.axis=1.2)
    mtext("Iteration number",side=1,line=-1.0,cex=1.1)
    mtext("Step length used",side=2,line=2.3,cex=1.1)
    lines(1:ti,moo[,5],col=moo[,1],lwd=2)
    abline(v=nil,lty=2)
    abline(h=refline[2],lty=2)

  par(oldpar)  # reset graphical parameters
}

########################################################################################################################################
# Visualize final grid
########################################################################################################################################
showgrid <- function(y){
  k <- length(y$t)
  space <- y$t[2:k]-y$t[1:(k-1)]
  plot(y$t[2:k],space,type="l",xlab="Ability",ylab="Space between gridpoints",log="y")
  abline(v=y$h1[,1], col=2, lty=3)
}

########################################################################################################################################
# Adapt grid: at all interval boundaries, place nnn new theta values to the left and to the right with spacing nsp
# nnn = number new nodes
# nsp = node spacing
# ig  = inner grid between -ig and ig
########################################################################################################################################
adaptgrid <- function(t,y,nnn=10,nsp=0.0001,ig=3){
  n  <- length(t)
  dd <- y$dd
  xi <- y$xi
  vi <- idwv(dd,xi)$vio    # Violations

  tn <- t  # new grid
  # add points around interval boundaries if there is a violation of the equivalence theorem, spacing multiplied with 10 if ability < -ig or >ig
  for (i in 2:(n-1)) {
    if (vi[i]>0 && (xi[i]!=xi[i-1] || xi[i]!=xi[i+1])) {
      if (abs(t[i])>ig) { tn <- c(tn,seq(t[i],t[i]-nnn*nsp*10,by=-nsp*10),seq(t[i],t[i]+nnn*nsp*10,by=nsp*10)) }
        else { tn <- c(tn,seq(t[i],t[i]-nnn*nsp,by=-nsp),seq(t[i],t[i]+nnn*nsp,by=nsp)) }
    }
  }
  unique(round(sort(tn),10))
}

########################################################################################################################################
# Consolidate design by removing small intervals of size < ex and adding half of them to the left larger and half to the right larger
# interval
########################################################################################################################################
consolidate <- function(h,ex=0.01){
  hv  <- h[,1]                         # interval boundaries
  k   <- length(hv)                    
  dhv <- c(99,hv[2:k]-hv[1:(k-1)])     # differences to last boundaries
  fl  <- (dhv<ex)                      # flag if interval smaller than ex
  nfl <- c(fl[2:k],0)                  # flag if next interval smaller than ex
  hm  <- cbind(hv,dhv,h[,3],fl,nfl)    # create matrix hm, third column is item to calibrate on interval prior to boundary
  hm1 <- hm[fl==0,]                    # keep only intervals larger than ex
  hv1 <- hm1[,1]
  k1  <- length(hv1)
  pv  <- rep(NA,k1)
  hi1 <- hm1[,3]                       # vector with item numbers to be calibrated
  hn1 <- c(hi1[2:k1],hi1[k1])          # same as before but for the next interval (shifted vector)
  pv[1] <- pnorm(hv1[1])
  for (i in 1:(k1-1)){
    if (hm1[i,5]==1) hv1[i] <- (hm1[i,1]+hm1[i+1,1]-hm1[i+1,2])/2  # divide length of deleted intervals into halfs and add to adjacent
    if (i>1) pv[i] <- pnorm(hv1[i])-pnorm(hv1[i-1])                # create probability to be in interval
  }
  pv[k1] <- 1-pnorm(hv1[k1-1])  
  cbind(hv1,pv,hi1,hn1)
}

########################################################################################################################################
# optical - outer loop for maximization process
# Hyper parameters for optimization: 
#  ip:      matrix with item parameters for all items (number of rows determins number of items)
#  imf:     the vector of step-lengths, initially c(0.05,0.1,0.15,0.2,0.25,0.3,0.35,0.4,0.45), but now c(0.05,0.1,0.2,0.45)
#  maxiter: maximal number of iterations in each inner loop, the length of this vector defines the number of outer loops
#  eps:     convergence criterion (maximum violation of eq.th.), vector with value for each inner loop, 
#           but the same number for all inner loops is recommended
#  nnn:     number of new nodes added at each position in the adaptive grid, vector with value for each inner loop (nnn[1] not used)
#  nsp:     node spacing between new nodes, vector with value for each inner loop (nsp[1] is the spacing between nodes of the starting grid)
#  sss:     step size stopping criterion
#  falpha:  factor alpha for adjusting the step size vector
#  sdr:     stop if design repeated (flag TRUE/FALSE)
#  ig:      inner grid between -ig and ig
#  ex:      intervals of size < ex will be removed (consolidate); if ex=0, no consolidation will be done
# Result of this function is a list with following instances:
#  $dd      directional derivatives of optimal solution
#  $xi      optimal solution
#  $t       final grid of ability values which was used
#  $viomax  largest violation of eq.th. from final solution (if < eps, alg. has converged, otherwise not)
#  $h1      interval boundaries for optimal solution
#  $mooiter monitoring iterations; information about each iteration to produce convergence plots
#  $time    running time of algorithm in minutes
########################################################################################################################################
optical <- function(ip,
                    imf=c(0.005,0.01,0.02,0.05,0.1,0.2,0.45),maxiter=rep(300,6),eps=rep(0.002,6),
                    nnn=c(0,50,50,200,200,200),nsp=c(0.001,0.0001,0.0001,0.00001,0.00001,0.00001),sss=0.001,falpha=1.08,sdr=TRUE,ig=3,ex=0){
  starttime <- proc.time()
  # starting grid with node spacing nsp[1] between -ig and ig and spacing 10*nsp[1] between -7 and -ig and between ig and 7
  t   <- c(seq(-ig,-7,by=-nsp[1]*10),seq(0,-ig,by=-nsp[1]),seq(0,ig,by=nsp[1]),seq(ig,7,by=nsp[1]*10))
  t   <- unique(sort(t))
  xis <- start.design(t,ip)                  # starting design

  oitermax  <- min(length(maxiter),length(eps),length(nnn),length(nsp))     # total number of outer iterations
  oiterc    <- 1                                                            # counter for outer iterations
  print(paste("---> Outer iteration =",oiterc))
  # Run optimization (maxiter = maximum number of iterations, eps = stopping criterion for maximum violation of equivalence criterion)
  yy  <- innerloop(t,ip,imf,maxiter=maxiter[oiterc],eps=eps[oiterc],sss=sss,falpha=falpha,sdr=sdr,xi=xis) 
  h1  <- intbounds(yy$xi,t)                  # Create boundaries for theta values
  if (ex>0) h1  <- consolidate(h1,ex=ex)
  mooiter <- cbind(oiterc,yy$moiter)         # Monitor outer (and inner) iterations
  while (oiterc<oitermax){
    oiterc <- oiterc+1
    if (yy$viomax>eps[oiterc]){
      # Adapt grid automatically
      print(paste("---> Adapt grid; outer iteration =",oiterc))
      t   <- adaptgrid(t,yy,nnn=nnn[oiterc],nsp=nsp[oiterc],ig=ig)
      xis <- start.design1(t,h1)
      # Run optimization 
      yy  <- innerloop(t,ip,imf,maxiter=maxiter[oiterc],eps=eps[oiterc],sss=sss,falpha=falpha,sdr=sdr,xi=xis) 
      h1  <- intbounds(yy$xi,t)              # Create boundaries for theta values
      if (ex>0) h1 <- consolidate(h1,ex=ex)
      mooiter <- rbind(mooiter,cbind(oiterc,yy$moiter))
    }
  }
  if (yy$viomax>eps[oiterc]) { print(paste0("Failed to converge. Maximum violation of eq.th.=", round(yy$viomax,5), " instead of ",eps[oiterc],".")) }
  # Time in minutes
  runtime <- (proc.time()-starttime)/60
  list(dd=yy$dd,xi=yy$xi,t=t,viomax=yy$viomax,h1=h1,mooiter=mooiter,time=runtime)
}

########################################################################################################################################
########################################################################################################################################
# Define here (ip) the prior guesses for the parameters of the items:
# each item in a row, first discrimination (a), then difficulty (b), then guessing parameter (c)
########################################################################################################################################
# Here an example for a 3PL model
ip <- cbind(c(1, 2, 2.5),
            c(-1.5, 0.5, 2),
            c(0.2, 0.1, 0.05))

# Here an example for a mixed 2/3PL model
ip <- cbind(c(0.8, 1.5, 2.0, 2.8),
            c(-0.5, -2, 0.5, 2),
            c(NA, NA, 0.1, 0.2))

# Here an example for a 2PL model
ip <- cbind(c( 4, 4, 4, 4, 4, 4, 4),
            c(-3,-2,-1, 0, 1, 2, 3))

########################################################################################################################################
# Call function optical
# For explanation of hyperparameters and the instances of the result see where the function is defined
########################################################################################################################################
# call recommended for 2-4 items:
yyy <- optical(ip, imf=c(0.005,0.01,0.02,0.05,0.1,0.2,0.45),maxiter=rep(300,6),eps=rep(0.002,6),
               nnn=c(0,50,50,200,200,200),nsp=c(0.001,0.0001,0.0001,0.00001,0.00001,0.00001),sss=0.001,falpha=1.08,ig=3,ex=0)
# Time in minutes:
yyy$time*60
########################################################################################################################################
# Illustration of result: Check visually if equivalence theorem is (approximately) fulfilled
# For description of different layout types, see text before function finalgraph 
########################################################################################################################################
drawdesign(yyy=yyy, ip=ip, ylowl=-60,refline=0.002,layout=1)
convergenceplot(moo=yyy$mooiter,refline=c(0.002,0.001*0.005/0.45))

# call if large precision desired for more than 4 items (tested for 5 items):
yyy <- optical(ip, imf=c(0.005,0.015,0.05,0.15,0.45),maxiter=rep(300,16),eps=rep(0.002,16),
               nnn=c(0,0,rep(200,4),rep(800,10)),
               nsp=c(0.001,0.001,rep(0.0001,2),rep(0.000025,4),rep(0.00000625,8)),sss=0.0001,falpha=1.08,ig=5,ex=0)
# Time in minutes:
yyy$time*60

yyy$h1     # Boundaries for intervals of optimal design


