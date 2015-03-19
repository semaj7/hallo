open util/boolean

abstract sig Profile{
	name:Name
}

sig PersonalProfile extends Profile{
	eMail:one EMail,
	friends:set PersonalProfile,
	following:set Profile,
	posted: set Content,
	isMember: set Member,
	canSee: set Content	
}
fact symmetric_friends{all disjoint p,q:PersonalProfile | p in q.friends => q in p.friends}

sig Name{}
fact unique_names{all disjoint p,q:Profile | p.name != q.name}
//fact names_are_connected{Name in Profile.name}

sig EMail{}
fact unique_Emails{all disjoint p,q:PersonalProfile | p.eMail != q.eMail}
fact eMail_are_connected{EMail in PersonalProfile.eMail}

fact no_reflexiv_friends{all p:Profile | not p in p.friends} 
fact no_reflexiv_followers{all p:Profile | not p in p.following}

--what can a group post?
sig GroupProfile extends Profile {
	posted: CommentableContent
}
fact groupcontent_is_public/privat{all g:GroupProfile,c:CommentableContent |
						c in g.posted => (c.visible = Public || c.visible = Private)}

--== is this true?
fact one_admin_per_group{some m:Member, g:GroupProfile | m.memberOf=g => isTrue[m.isAdmin]}

//can a member be member and follow a group?

sig Member {
	isAdmin:Bool,
	memberOf: one GroupProfile
}
fact unique_members{all disjoint p,q:PersonalProfile, m:Member | m in p.isMember => not m in q.isMember}
fact members_are_connected{Member in PersonalProfile.isMember}

fact only_once_member_of_a_group{
all p:PersonalProfile, disjoint m,n:Member, g:GroupProfile | (g=m.memberOf && m in p.isMember) => not (g=n.memberOf && n in p.isMember)}

--fact atLeast_one_admin_per_group



sig Content{
	visible: Visible
}
fact unique_personalPosts{all disjoint p,q:PersonalProfile, c:Content | c in p.posted => not c in q.posted}
fact unique_groupPosts{all disjoint p,q:GroupProfile, c:Content | c in p.posted => not c in q.posted}
//fact unique_posts{all p:PersonalProfile, q:GroupProfile, c:Content | c in p.posted => not c in q.posted}

fact post_are_connected{Content in PersonalProfile.posted}

abstract sig CommentableContent extends Content{}
abstract sig PersonalContent extends Content{}

sig Photo extends CommentableContent{}
sig Post extends CommentableContent{
	post: String,
	link: set Photo
}
sig Comment extends CommentableContent{
	comment: String,
	refersTo: set CommentableContent
}

sig PersonalMessage extends PersonalContent{
	message: String,
	includedPhoto: lone Photo 	
}
sig PersonalDetails extends PersonalContent{
	details:String
}

abstract sig Visible {}
one sig Private, Friends, FriendsOfFriends, TransitiveFriends, Public extends Visible{}

fact canSee{all disjoint p:PersonalProfile,c:Content | 
		(c in p.posted ||
		(c.visible = Friends && c in p.friends.posted) ||
		(c.visible = FriendsOfFriends && (c in p.friends.posted || c in p.friends.friends.posted)) ||
		(c.visible = TransitiveFriends && c in p.^friends.posted) ||
		(c.visible = Public))
		=> c in p.canSee }

pred show() {
	all p:PersonalProfile | #p.following >= 1
	all p:PersonalProfile | #p.friends >= 1
	all p:PersonalProfile | #p.posted >= 2
	some p:PersonalProfile | #p.isMember >= 2

//	#Photo >=5
//	#PersonalProfile >= 2
//	#GroupProfile

}

run show for 4 //but 4 Member
	
